#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
一鍵影片下載器 - 佇列增強版 (支援 YouTube、X / Twitter、Instagram、TikTok 等平台)
================================================================================
本程式使用 Python 內建的 Tkinter 建立桌面圖形介面，並透過開源套件 `yt-dlp`
解析與下載公開、無 DRM 保護之影音串流。

功能特點：
1. 內建「下載網址佇列 (Queue)」：下載進行中仍可隨時貼上新網址排隊、支援一次貼上多行網址批次排程、
   即時顯示每筆任務狀態與進度，並提供移除選取、清除已完成與失敗重試功能。
2. 強制優先選用高相容性 H.264 (avc1) + AAC (m4a) 編碼，避開 Windows 預設播放器不支援的 AV1 (av01) 編碼，
   確保下載後的 MP4 在任何 Windows / macOS / 手機播放器都能直接播放畫面與聲音。
3. 自動安裝並配置 `yt-dlp` 與 `imageio-ffmpeg`（支援 1080p/4K 影音合併與 MP3 轉檔）。
4. 針對 X (Twitter) 敏感內容／年齡限制貼文或引用推文，內建三層智慧解析：
   - 支援選用瀏覽器 Cookies 或匯入 `cookies.txt`。
   - 若未登入導致 X 阻擋訪客讀取（出現 No video could be found / Video is unavailable），
     自動透過 FxTwitter / VxTwitter 公開 API 解析出底層 `video.twimg.com` 直連串流並完成下載。
5. 相容 PyInstaller 單一 `.exe` 執行檔打包。
"""

import importlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import tkinter as tk
import urllib.request
from dataclasses import dataclass
from tkinter import filedialog, messagebox, ttk

try:
    import yt_dlp
except ImportError:
    yt_dlp = None

try:
    import imageio_ffmpeg
except ImportError:
    imageio_ffmpeg = None


ANSI_ESCAPE_RE = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")
X_STATUS_RE = re.compile(
    r"https?://(?:www\.|mobile\.)?(?:x\.com|twitter\.com)/(?:([^/?#]+)/status|i/web/status)/(\d+)",
    re.IGNORECASE,
)

FORMAT_LABELS = {
    "best_mp4": "最高畫質 MP4 (H.264)",
    "1080p_mp4": "1080p MP4 (H.264)",
    "720p_mp4": "720p MP4 (H.264)",
    "audio_mp3": "音訊 MP3/M4A",
}


@dataclass
class QueueTask:
    task_id: int
    url: str
    save_dir: str
    fmt_choice: str
    status: str = "⏳ 等待中"
    title: str = ""


def strip_ansi(text: str) -> str:
    """移除終端機顏色控制碼（如 [0;31m）。"""
    return ANSI_ESCAPE_RE.sub("", text)


def is_frozen_exe() -> bool:
    """判斷目前是否正以 PyInstaller 打包後的 .exe 執行檔模式運作。"""
    return bool(getattr(sys, "frozen", False))


def resolve_x_video_fallback(url: str) -> tuple[str | None, str | None]:
    """
    當 X (Twitter) 因未登入訪客限制回傳 No video could be found / Video is unavailable 時，
    自動透過公開的 FxTwitter / VxTwitter API 解析出直連影片網址 (video.twimg.com)。
    回傳 (direct_video_url, title)。
    """
    match = X_STATUS_RE.search(url)
    if not match:
        return None, None

    user = match.group(1) or "i"
    tweet_id = match.group(2)
    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"}

    # 1. 嘗試 FxTwitter API (支援本體推文與 Quote 引用推文)
    fx_api = f"https://api.fxtwitter.com/{user}/status/{tweet_id}"
    try:
        req = urllib.request.Request(fx_api, headers=headers)
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        tweet = data.get("tweet") or {}
        for target in (tweet, tweet.get("quote") or {}):
            media = target.get("media") or {}
            videos = media.get("videos") or []
            if videos and isinstance(videos[0], dict) and videos[0].get("url"):
                author = (target.get("author") or {}).get("screen_name") or user
                text = (target.get("text") or "").strip().replace("\n", " ")[:50]
                title = f"X_{author}_{tweet_id}" + (f"_{text}" if text else "")
                return videos[0]["url"], title
            for item in media.get("all") or []:
                if item.get("type") in ("video", "gif") and item.get("url"):
                    return item["url"], f"X_{user}_{tweet_id}"
    except Exception:
        pass

    # 2. 嘗試 VxTwitter API 備援
    vx_api = f"https://api.vxtwitter.com/{user}/status/{tweet_id}"
    try:
        req = urllib.request.Request(vx_api, headers=headers)
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8", errors="ignore"))
        for target in (data, data.get("qrt") or {}):
            for item in target.get("media_extended") or []:
                if item.get("type") in ("video", "gif") and item.get("url"):
                    author = target.get("user_screen_name") or user
                    return item["url"], f"X_{author}_{tweet_id}"
    except Exception:
        pass

    return None, None


class OneClickVideoDownloader(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title("一鍵影片下載器 (支援多筆網址佇列排程)")
        self.geometry("780x680")
        self.minsize(700, 600)
        self.configure(padx=16, pady=14)

        self.is_worker_running = False
        self.active_task_id: int | None = None
        self.next_task_id = 1
        self.tasks: dict[int, QueueTask] = {}
        self.task_order: list[int] = []

        self.ffmpeg_path: str | None = None
        self.cookie_file_path: str = ""
        self.default_save_dir = os.path.join(os.path.expanduser("~"), "Downloads")
        if not os.path.isdir(self.default_save_dir):
            self.default_save_dir = os.getcwd()

        self._build_ui()
        threading.Thread(target=self._init_environment, daemon=True).start()

    def _init_environment(self) -> None:
        """檢查環境（若為 .py 腳本模式則自動補裝套件），並定位內建或系統的 ffmpeg。"""
        global yt_dlp, imageio_ffmpeg

        if not is_frozen_exe():
            missing_pkgs = []
            if yt_dlp is None:
                missing_pkgs.append("yt-dlp")
            if shutil.which("ffmpeg") is None and imageio_ffmpeg is None:
                missing_pkgs.append("imageio-ffmpeg")

            if missing_pkgs:
                self.append_log(f"⏳ 正在自動安裝必要元件 ({', '.join(missing_pkgs)})，請稍候...")
                try:
                    subprocess.check_call(
                        [sys.executable, "-m", "pip", "install", "-U", *missing_pkgs],
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                    )
                    if yt_dlp is None:
                        yt_dlp = importlib.import_module("yt_dlp")
                    if imageio_ffmpeg is None:
                        try:
                            imageio_ffmpeg = importlib.import_module("imageio_ffmpeg")
                        except ImportError:
                            pass
                    self.append_log("✅ 必要元件自動安裝完成！")
                except Exception as exc:
                    self.append_log(f"⚠️ 自動安裝部分元件失敗：{exc}")

        self.ffmpeg_path = self._resolve_ffmpeg_path()
        if self.ffmpeg_path:
            self.append_log(
                f"✔ 已就緒（已啟用 FFmpeg 與 H.264 高相容編碼：{os.path.basename(self.ffmpeg_path)}）"
            )
        else:
            self.append_log(
                "ℹ️ 未偵測到系統 FFmpeg，將自動使用「免合併單一串流模式 (H.264)」下載影片。"
            )

    def _resolve_ffmpeg_path(self) -> str | None:
        """優先尋找系統 PATH 中的 ffmpeg，若無則使用 imageio-ffmpeg 內建執行檔。"""
        sys_ffmpeg = shutil.which("ffmpeg")
        if sys_ffmpeg:
            return sys_ffmpeg

        if imageio_ffmpeg is not None:
            try:
                raw_exe = imageio_ffmpeg.get_ffmpeg_exe()
                if raw_exe and os.path.isfile(raw_exe):
                    cache_dir = os.path.join(os.path.expanduser("~"), ".yt_dlp_ffmpeg")
                    os.makedirs(cache_dir, exist_ok=True)
                    exe_name = "ffmpeg.exe" if os.name == "nt" else "ffmpeg"
                    target_exe = os.path.join(cache_dir, exe_name)
                    if not os.path.isfile(target_exe):
                        shutil.copy2(raw_exe, target_exe)
                    return target_exe
            except Exception:
                pass
        return None

    def _build_ui(self) -> None:
        # 1. 網址輸入區
        url_frame = ttk.LabelFrame(
            self, text=" 1. 新增影片網址 (支援單筆或一次貼上多行網址加入佇列) ", padding=10
        )
        url_frame.pack(fill=tk.X, pady=(0, 8))

        self.url_var = tk.StringVar()
        self.url_entry = ttk.Entry(url_frame, textvariable=self.url_var, font=("Segoe UI", 10))
        self.url_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        self.url_entry.bind("<Return>", lambda _e: self.add_entry_to_queue())

        paste_queue_btn = ttk.Button(
            url_frame, text="貼上並加入佇列", command=self.paste_and_enqueue
        )
        paste_queue_btn.pack(side=tk.RIGHT)

        add_queue_btn = ttk.Button(
            url_frame, text="加入佇列", command=self.add_entry_to_queue
        )
        add_queue_btn.pack(side=tk.RIGHT, padx=(0, 6))

        # 2. 下載設定區
        options_frame = ttk.LabelFrame(self, text=" 2. 下載設定 ", padding=10)
        options_frame.pack(fill=tk.X, pady=(0, 8))

        # 儲存資料夾
        dir_row = ttk.Frame(options_frame)
        dir_row.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(dir_row, text="儲存位置：", width=10).pack(side=tk.LEFT)
        self.save_dir_var = tk.StringVar(value=self.default_save_dir)
        dir_entry = ttk.Entry(dir_row, textvariable=self.save_dir_var)
        dir_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 8))
        ttk.Button(dir_row, text="選擇資料夾...", command=self.choose_directory).pack(side=tk.RIGHT)

        # 畫質與格式選擇
        fmt_row = ttk.Frame(options_frame)
        fmt_row.pack(fill=tk.X, pady=(0, 6))
        ttk.Label(fmt_row, text="輸出格式：", width=10).pack(side=tk.LEFT)

        self.format_var = tk.StringVar(value="best_mp4")
        formats = [
            ("最高畫質 MP4 (H.264 相容)", "best_mp4"),
            ("1080p MP4 (H.264 相容)", "1080p_mp4"),
            ("720p MP4 (H.264 相容)", "720p_mp4"),
            ("僅擷取音訊 (MP3/M4A)", "audio_mp3"),
        ]
        for label, val in formats:
            ttk.Radiobutton(fmt_row, text=label, value=val, variable=self.format_var).pack(
                side=tk.LEFT, padx=(0, 12)
            )

        # 登入憑證選擇與自動啟動勾選
        auth_row = ttk.Frame(options_frame)
        auth_row.pack(fill=tk.X)
        ttk.Label(auth_row, text="帳號憑證：", width=10).pack(side=tk.LEFT)

        self.auth_combo = ttk.Combobox(
            auth_row,
            state="readonly",
            width=34,
            values=[
                "免登入 (公開影片 + X 敏感內容自動備援)",
                "選擇 cookies.txt 憑證檔 (推薦用於私人/限制影片)",
                "讀取 Firefox 瀏覽器登入狀態",
                "讀取 Edge 瀏覽器登入狀態 (需先關閉 Edge)",
                "讀取 Chrome 瀏覽器登入狀態 (需先關閉 Chrome)",
            ],
        )
        self.auth_combo.current(0)
        self.auth_combo.pack(side=tk.LEFT, padx=(0, 8))
        self.auth_combo.bind("<<ComboboxSelected>>", self._on_auth_changed)

        self.cookie_btn = ttk.Button(
            auth_row, text="選擇 cookies.txt...", command=self.choose_cookie_file
        )
        self.cookie_btn.pack(side=tk.LEFT, padx=(0, 12))

        self.auto_start_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(
            auth_row, text="加入佇列後自動開始下載", variable=self.auto_start_var
        ).pack(side=tk.RIGHT)

        # 3. 下載佇列區 (Queue Treeview)
        queue_frame = ttk.LabelFrame(self, text=" 3. 下載佇列 (可隨時新增網址排隊) ", padding=10)
        queue_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 8))

        tree_container = ttk.Frame(queue_frame)
        tree_container.pack(fill=tk.BOTH, expand=True, pady=(0, 6))

        columns = ("id", "status", "format", "url")
        self.queue_tree = ttk.Treeview(
            tree_container, columns=columns, show="headings", height=6, selectmode="extended"
        )
        self.queue_tree.heading("id", text="#")
        self.queue_tree.heading("status", text="狀態")
        self.queue_tree.heading("format", text="輸出格式")
        self.queue_tree.heading("url", text="影片網址 / 標題")

        self.queue_tree.column("id", width=45, anchor=tk.CENTER, stretch=False)
        self.queue_tree.column("status", width=135, anchor=tk.W, stretch=False)
        self.queue_tree.column("format", width=140, anchor=tk.CENTER, stretch=False)
        self.queue_tree.column("url", width=400, anchor=tk.W, stretch=True)

        q_scroll = ttk.Scrollbar(tree_container, orient=tk.VERTICAL, command=self.queue_tree.yview)
        self.queue_tree.configure(yscrollcommand=q_scroll.set)
        self.queue_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        q_scroll.pack(side=tk.RIGHT, fill=tk.Y)

        # 佇列管理與進度條列
        queue_ctrl_row = ttk.Frame(queue_frame)
        queue_ctrl_row.pack(fill=tk.X)

        ttk.Button(queue_ctrl_row, text="移除選取", command=self.remove_selected_tasks).pack(
            side=tk.LEFT, padx=(0, 6)
        )
        ttk.Button(queue_ctrl_row, text="清除已完成", command=self.clear_completed_tasks).pack(
            side=tk.LEFT, padx=(0, 6)
        )
        ttk.Button(queue_ctrl_row, text="失敗重試", command=self.retry_failed_tasks).pack(
            side=tk.LEFT, padx=(0, 6)
        )
        ttk.Button(queue_ctrl_row, text="清空等待中", command=self.clear_pending_tasks).pack(
            side=tk.LEFT, padx=(0, 12)
        )

        self.progress_var = tk.DoubleVar(value=0.0)
        self.progress_bar = ttk.Progressbar(
            queue_ctrl_row, variable=self.progress_var, maximum=100.0, mode="determinate"
        )
        self.progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))

        self.start_queue_btn = ttk.Button(
            queue_ctrl_row, text="▶ 開始佇列下載", command=self.ensure_worker_running
        )
        self.start_queue_btn.pack(side=tk.RIGHT)

        # 4. 狀態與日誌區
        log_frame = ttk.LabelFrame(self, text=" 4. 執行日誌 ", padding=10)
        log_frame.pack(fill=tk.BOTH, expand=True)

        self.log_text = tk.Text(
            log_frame, height=7, state=tk.DISABLED, wrap=tk.WORD, font=("Consolas", 9)
        )
        scrollbar = ttk.Scrollbar(log_frame, orient=tk.VERTICAL, command=self.log_text.yview)
        self.log_text.configure(yscrollcommand=scrollbar.set)
        self.log_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        self.append_log(
            "準備就緒。預設已啟用 H.264 (AVC) 高相容視訊編碼，避免 Windows 內建播放器出現 AV1 無法播放的問題。"
        )

    def _on_auth_changed(self, _event: object = None) -> None:
        idx = self.auth_combo.current()
        if idx == 1 and not self.cookie_file_path:
            self.choose_cookie_file()

    def choose_cookie_file(self) -> None:
        selected = filedialog.askopenfilename(
            title="選擇 Netscape 格式的 cookies.txt 檔案",
            filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
        )
        if selected:
            self.cookie_file_path = selected
            self.auth_combo.current(1)
            self.append_log(f"🍪 已載入憑證檔：{selected}")

    def append_log(self, message: str) -> None:
        """在執行日誌視窗新增一行文字（執行緒安全）。"""
        clean_msg = strip_ansi(message)

        def _update() -> None:
            self.log_text.configure(state=tk.NORMAL)
            self.log_text.insert(tk.END, clean_msg + "\n")
            self.log_text.see(tk.END)
            self.log_text.configure(state=tk.DISABLED)

        self.after(0, _update)

    def _extract_urls_from_text(self, raw_text: str) -> list[str]:
        """從單行或多行文字中分離出有效網址清單。"""
        candidates = [token.strip() for token in re.split(r"[\r\n\s]+", raw_text) if token.strip()]
        urls = [u for u in candidates if u.startswith(("http://", "https://"))]
        if not urls and raw_text.strip():
            urls = [raw_text.strip()]
        return urls

    def enqueue_urls(self, urls: list[str]) -> int:
        """將一或多筆網址加入下載佇列，回傳成功加入的數量。"""
        save_dir = self.save_dir_var.get().strip()
        if not os.path.isdir(save_dir):
            messagebox.showerror("路徑無效", f"找不到指定的儲存資料夾：\n{save_dir}")
            return 0

        fmt_choice = self.format_var.get()
        fmt_label = FORMAT_LABELS.get(fmt_choice, fmt_choice)
        added = 0

        for url in urls:
            task_id = self.next_task_id
            self.next_task_id += 1
            task = QueueTask(
                task_id=task_id,
                url=url,
                save_dir=save_dir,
                fmt_choice=fmt_choice,
            )
            self.tasks[task_id] = task
            self.task_order.append(task_id)
            self.queue_tree.insert(
                "",
                tk.END,
                iid=str(task_id),
                values=(task_id, task.status, fmt_label, task.url),
            )
            added += 1

        if added > 0:
            self.append_log(f"➕ 已將 {added} 筆網址加入佇列。")
            if self.auto_start_var.get():
                self.ensure_worker_running()
        return added

    def add_entry_to_queue(self) -> None:
        """將輸入框中的網址加入佇列並清空輸入框。"""
        raw = self.url_var.get().strip()
        if not raw:
            messagebox.showwarning("請輸入網址", "請先輸入或貼上要加入佇列的影片網址。")
            return
        urls = self._extract_urls_from_text(raw)
        if self.enqueue_urls(urls) > 0:
            self.url_var.set("")

    def paste_and_enqueue(self) -> None:
        """從系統剪貼簿讀取單筆或多行網址，直接加入佇列並依設定自動啟動下載。"""
        try:
            clipboard_text = self.clipboard_get().strip()
        except tk.TclError:
            messagebox.showwarning("剪貼簿為空", "無法從剪貼簿讀取文字，請手動貼上網址。")
            return

        if not clipboard_text:
            messagebox.showwarning("剪貼簿為空", "剪貼簿中沒有網址內容。")
            return

        urls = self._extract_urls_from_text(clipboard_text)
        if self.enqueue_urls(urls) > 0:
            self.url_var.set("")

    def update_task_row(
        self, task_id: int, status: str | None = None, title: str | None = None
    ) -> None:
        """執行緒安全地更新佇列清單中的狀態與標題顯示。"""
        def _update() -> None:
            task = self.tasks.get(task_id)
            if not task:
                return
            if status is not None:
                task.status = status
            if title is not None:
                task.title = title
            iid = str(task_id)
            if self.queue_tree.exists(iid):
                fmt_label = FORMAT_LABELS.get(task.fmt_choice, task.fmt_choice)
                display_url = f"《{task.title}》 ({task.url})" if task.title else task.url
                self.queue_tree.item(
                    iid, values=(task.task_id, task.status, fmt_label, display_url)
                )

        self.after(0, _update)

    def remove_selected_tasks(self) -> None:
        """移除使用者在佇列中選取的項目（正在下載中的項目除外）。"""
        selected = self.queue_tree.selection()
        if not selected:
            return
        for iid in selected:
            tid = int(iid)
            if tid == self.active_task_id:
                messagebox.showinfo("無法移除", f"任務 #{tid} 目前正在下載中，無法直接移除。")
                continue
            self.queue_tree.delete(iid)
            self.tasks.pop(tid, None)
            if tid in self.task_order:
                self.task_order.remove(tid)

    def clear_completed_tasks(self) -> None:
        """清除所有已完成的佇列項目。"""
        for tid in list(self.task_order):
            task = self.tasks.get(tid)
            if task and task.status.startswith("✅"):
                iid = str(tid)
                if self.queue_tree.exists(iid):
                    self.queue_tree.delete(iid)
                self.tasks.pop(tid, None)
                self.task_order.remove(tid)

    def clear_pending_tasks(self) -> None:
        """清空所有尚在等待中的佇列項目。"""
        for tid in list(self.task_order):
            task = self.tasks.get(tid)
            if task and task.status.startswith("⏳"):
                iid = str(tid)
                if self.queue_tree.exists(iid):
                    self.queue_tree.delete(iid)
                self.tasks.pop(tid, None)
                self.task_order.remove(tid)

    def retry_failed_tasks(self) -> None:
        """將所有失敗的任務重設為等待中，並啟動佇列下載。"""
        retried = 0
        for tid in self.task_order:
            task = self.tasks.get(tid)
            if task and task.status.startswith("❌"):
                self.update_task_row(tid, status="⏳ 等待中")
                retried += 1
        if retried > 0:
            self.append_log(f"🔄 已將 {retried} 筆失敗任務重新排入佇列。")
            self.ensure_worker_running()

    def choose_directory(self) -> None:
        selected = filedialog.askdirectory(initialdir=self.save_dir_var.get())
        if selected:
            self.save_dir_var.set(selected)

    def _build_ydl_opts(
        self,
        save_dir: str,
        fmt_choice: str,
        use_ffmpeg: bool,
        custom_title: str | None = None,
    ) -> dict:
        """
        根據使用者選擇的格式與是否具備 FFmpeg 建立 yt-dlp 設定參數。
        強制優先選用 H.264 (avc1) 視訊軌與 AAC (m4a) 音訊軌，避開 Windows 預設不支援的 AV1 (av01) 編碼。
        """
        if custom_title:
            safe_title = re.sub(r'[\\/*?:"<>|]', "_", custom_title)
            output_template = os.path.join(save_dir, f"{safe_title}.%(ext)s")
        else:
            output_template = os.path.join(save_dir, "%(title).120s [%(id)s].%(ext)s")

        common_opts: dict = {
            "outtmpl": output_template,
            "noplaylist": True,
            "progress_hooks": [self._progress_hook],
            "quiet": True,
            "no_warnings": True,
            "no_color": True,
            # 排序優先權：強制 H.264 (avc1) 視訊編碼與 m4a (AAC) 音訊優先於 AV1 / VP9
            "format_sort": ["vcodec:h264", "acodec:m4a"],
        }

        auth_idx = self.auth_combo.current()
        if auth_idx == 1 and self.cookie_file_path and os.path.isfile(self.cookie_file_path):
            common_opts["cookiefile"] = self.cookie_file_path
        elif auth_idx == 2:
            common_opts["cookiesfrombrowser"] = ("firefox",)
        elif auth_idx == 3:
            common_opts["cookiesfrombrowser"] = ("edge",)
        elif auth_idx == 4:
            common_opts["cookiesfrombrowser"] = ("chrome",)

        if use_ffmpeg and self.ffmpeg_path:
            common_opts["ffmpeg_location"] = self.ffmpeg_path

            if fmt_choice == "best_mp4":
                common_opts.update({
                    "format": (
                        "bestvideo[vcodec^=avc1][ext=mp4]+bestaudio[ext=m4a]/"
                        "bestvideo[vcodec!^=av01][ext=mp4]+bestaudio[ext=m4a]/"
                        "bestvideo[ext=mp4]+bestaudio[ext=m4a]/best[ext=mp4]/best"
                    ),
                    "merge_output_format": "mp4",
                })
            elif fmt_choice == "1080p_mp4":
                common_opts.update({
                    "format": (
                        "bestvideo[height<=1080][vcodec^=avc1][ext=mp4]+bestaudio[ext=m4a]/"
                        "bestvideo[height<=1080][vcodec!^=av01][ext=mp4]+bestaudio[ext=m4a]/"
                        "best[height<=1080][ext=mp4]/best[height<=1080]"
                    ),
                    "merge_output_format": "mp4",
                })
            elif fmt_choice == "720p_mp4":
                common_opts.update({
                    "format": (
                        "bestvideo[height<=720][vcodec^=avc1][ext=mp4]+bestaudio[ext=m4a]/"
                        "bestvideo[height<=720][vcodec!^=av01][ext=mp4]+bestaudio[ext=m4a]/"
                        "best[height<=720][ext=mp4]/best[height<=720]"
                    ),
                    "merge_output_format": "mp4",
                })
            elif fmt_choice == "audio_mp3":
                common_opts.update({
                    "format": "bestaudio/best",
                    "postprocessors": [{
                        "key": "FFmpegExtractAudio",
                        "preferredcodec": "mp3",
                        "preferredquality": "192",
                    }],
                })
        else:
            if fmt_choice == "best_mp4":
                common_opts["format"] = (
                    "best[vcodec^=avc1][ext=mp4]/best[vcodec!^=av01][ext=mp4]/best[ext=mp4]/best"
                )
            elif fmt_choice == "1080p_mp4":
                common_opts["format"] = (
                    "best[height<=1080][vcodec^=avc1][ext=mp4]/"
                    "best[height<=1080][vcodec!^=av01][ext=mp4]/"
                    "best[height<=1080][ext=mp4]/best[height<=1080]/best"
                )
            elif fmt_choice == "720p_mp4":
                common_opts["format"] = (
                    "best[height<=720][vcodec^=avc1][ext=mp4]/"
                    "best[height<=720][vcodec!^=av01][ext=mp4]/"
                    "best[height<=720][ext=mp4]/best[height<=720]/best"
                )
            elif fmt_choice == "audio_mp3":
                common_opts["format"] = "bestaudio[ext=m4a]/bestaudio/best"

        return common_opts

    def _progress_hook(self, d: dict) -> None:
        """接收 yt-dlp 的即時進度回呼並同步更新佇列狀態欄與進度條。"""
        status = d.get("status")
        tid = self.active_task_id
        if status == "downloading":
            total = d.get("total_bytes") or d.get("total_bytes_estimate") or 0
            downloaded = d.get("downloaded_bytes", 0)
            if total > 0:
                percent = (downloaded / total) * 100.0
                self.after(0, lambda p=percent: self.progress_var.set(p))
            speed_str = strip_ansi(d.get("_speed_str", "")).strip()
            eta_str = strip_ansi(d.get("_eta_str", "")).strip()
            pct_str = strip_ansi(d.get("_percent_str", "")).strip()
            if tid is not None:
                self.update_task_row(tid, status=f"⬇ 下載中 {pct_str}")
            self.after(
                0,
                lambda: self.title(
                    f"[#{tid}] 下載中 {pct_str} ({speed_str}, 剩餘 {eta_str}) - 一鍵影片下載器"
                ),
            )
        elif status == "finished":
            self.after(0, lambda: self.progress_var.set(100.0))
            if tid is not None:
                self.update_task_row(tid, status="⚙ 封裝處理中...")

    def _get_next_pending_task(self) -> QueueTask | None:
        for tid in self.task_order:
            task = self.tasks.get(tid)
            if task and task.status.startswith("⏳"):
                return task
        return None

    def ensure_worker_running(self) -> None:
        """若背景佇列執行緒尚未運行且有等待中的任務，立即啟動背景執行緒。"""
        if self.is_worker_running:
            return

        if yt_dlp is None:
            messagebox.showerror(
                "缺少必要套件",
                "找不到 yt-dlp 套件。\n請先開啟終端機執行：\npip install yt-dlp",
            )
            return

        if self._get_next_pending_task() is None:
            raw = self.url_var.get().strip()
            if raw:
                urls = self._extract_urls_from_text(raw)
                self.url_var.set("")
                self.enqueue_urls(urls)
                return
            messagebox.showinfo("佇列為空", "目前佇列中沒有等待下載的網址。")
            return

        self.is_worker_running = True
        self.start_queue_btn.configure(state=tk.DISABLED, text="⏳ 佇列執行中...")
        worker = threading.Thread(target=self._queue_worker_loop, daemon=True)
        worker.start()

    def _queue_worker_loop(self) -> None:
        """依序取出佇列中所有等待中的網址並逐一下載。"""
        if self.ffmpeg_path is None:
            self.ffmpeg_path = self._resolve_ffmpeg_path()

        try:
            while True:
                task = self._get_next_pending_task()
                if task is None:
                    break

                self.active_task_id = task.task_id
                self.after(0, lambda: self.progress_var.set(0.0))
                self.update_task_row(task.task_id, status="🔍 解析網址中...")
                self.append_log(f"▶ [任務 #{task.task_id}] 開始解析：{task.url}")

                self._process_single_task(task)

            self.append_log("🎉 佇列中的所有等待任務皆已處理完畢！\n")
        finally:
            def _reset_ui() -> None:
                self.active_task_id = None
                self.is_worker_running = False
                self.start_queue_btn.configure(state=tk.NORMAL, text="▶ 開始佇列下載")
                self.title("一鍵影片下載器 (支援多筆網址佇列排程)")

            self.after(0, _reset_ui)

    def _process_single_task(self, task: QueueTask) -> None:
        use_ffmpeg = self.ffmpeg_path is not None
        ydl_opts = self._build_ydl_opts(task.save_dir, task.fmt_choice, use_ffmpeg=use_ffmpeg)

        try:
            with yt_dlp.YoutubeDL(ydl_opts) as ydl:
                info = ydl.extract_info(task.url, download=True)
                title = info.get("title", "未知標題") if isinstance(info, dict) else "影片"
            self.update_task_row(task.task_id, status="✅ 完成", title=title)
            self.append_log(f"✅ [任務 #{task.task_id}] 下載成功：《{title}》")
            return
        except Exception as exc:
            err_msg = strip_ansi(str(exc))

            # 1. X (Twitter) 備援解析通道
            if X_STATUS_RE.search(task.url) and any(
                k in err_msg.lower()
                for k in ("no video could be found", "unavailable", "nsfw", "login", "guest")
            ):
                self.append_log(
                    f"🔄 [任務 #{task.task_id}] 啟動 X 備援解析通道..."
                )
                direct_url, custom_title = resolve_x_video_fallback(task.url)
                if direct_url:
                    try:
                        fb_opts = self._build_ydl_opts(
                            task.save_dir,
                            task.fmt_choice,
                            use_ffmpeg=use_ffmpeg,
                            custom_title=custom_title,
                        )
                        with yt_dlp.YoutubeDL(fb_opts) as ydl:
                            ydl.extract_info(direct_url, download=True)
                        self.update_task_row(
                            task.task_id, status="✅ 完成", title=custom_title or "X 影片"
                        )
                        self.append_log(
                            f"✅ [任務 #{task.task_id}] 透過 X 備援通道下載成功：《{custom_title}》"
                        )
                        return
                    except Exception as fb_exc:
                        err_msg = strip_ansi(str(fb_exc))

            # 2. 免 FFmpeg 單一串流降級重試
            if use_ffmpeg and "ffmpeg is not installed" in err_msg.lower():
                self.append_log(
                    f"ℹ️ [任務 #{task.task_id}] 切換為「免合併單一串流模式」重新下載..."
                )
                try:
                    fallback_opts = self._build_ydl_opts(
                        task.save_dir, task.fmt_choice, use_ffmpeg=False
                    )
                    with yt_dlp.YoutubeDL(fallback_opts) as ydl:
                        info = ydl.extract_info(task.url, download=True)
                        title = info.get("title", "未知標題") if isinstance(info, dict) else "影片"
                    self.update_task_row(task.task_id, status="✅ 完成", title=title)
                    self.append_log(f"✅ [任務 #{task.task_id}] 下載成功：《{title}》")
                    return
                except Exception as retry_exc:
                    err_msg = strip_ansi(str(retry_exc))

            self.update_task_row(task.task_id, status="❌ 失敗")
            self.append_log(f"❌ [任務 #{task.task_id}] 下載失敗：{err_msg}")


if __name__ == "__main__":
    app = OneClickVideoDownloader()
    app.mainloop()