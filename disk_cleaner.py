#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Disk Cleaner — поиск самых больших файлов на компьютере и их удаление.

Возможности:
  * два режима: «крупнейшие файлы» и «крупнейшие папки» (суммарный размер папки
    со всем содержимым, удаление папки целиком);
  * сканирование всех локальных дисков (или выбранных папок) в фоновом потоке —
    интерфейс остаётся отзывчивым, прогресс виден в реальном времени;
  * фильтр по минимальному размеру, топ-N, поиск по имени/пути;
  * таблица найденных файлов с чекбоксами, сортировкой по любой колонке;
  * удаление отмеченных файлов в Корзину (можно отменить) или безвозвратно;
  * защита системных папок и файлов от случайного удаления;
  * экспорт списка в CSV.

Запуск GUI:      python disk_cleaner.py
Только консоль:  python disk_cleaner.py --cli C:\\ --min-size-mb 200 --top 30
"""

from __future__ import annotations

import csv
import ctypes
import ctypes.wintypes
import heapq
import os
import queue
import shutil
import stat
import subprocess
import sys
import threading
import time
from datetime import datetime

APP_TITLE = "Disk Cleaner — поиск больших файлов"
APP_VERSION = "1.0"

# ---------------------------------------------------------------- оформление

BG      = "#16181d"   # фон окна
PANEL   = "#1e2127"   # панели, заголовки таблицы
CARD    = "#22252c"   # тело таблицы
CARD2   = "#262a31"   # зебра
HOVER   = "#2f343d"
BORDER  = "#333941"
FG      = "#e8eaed"
MUTED   = "#98a2b3"
ACCENT  = "#4c9aff"
ACCENT2 = "#7cb8ff"
DANGER  = "#e5534b"
DANGER2 = "#ff6f66"
OK      = "#3fb950"
SELECT  = "#2f4f7f"
GOLD    = "#e3b341"

FONT = "Segoe UI"
MONO = "Consolas"

# Файлы, которые нельзя удалять ни при каких условиях
SYSTEM_FILES = {
    "pagefile.sys", "hiberfil.sys", "swapfile.sys",
    "dumpstack.log.tmp", "bootmgr", "ntldr", "boot.ini",
}

# Папки, содержимое которых защищено от удаления
PROTECTED_DIRS = [
    r"c:\windows",
    r"c:\program files",
    r"c:\program files (x86)",
    r"c:\programdata",
    r"c:\$recycle.bin",
    r"c:\system volume information",
    r"c:\recovery",
    r"c:\boot",
    r"c:\perflogs",
    r"c:\msocache",
]

# Эти папки можно не обходить при сканировании (ускоряет и убирает шум)
SKIP_DIRS_DEFAULT = [
    r"c:\windows",
    r"c:\program files",
    r"c:\program files (x86)",
    r"c:\programdata",
    r"c:\$recycle.bin",
    r"c:\system volume information",
    r"c:\recovery",
    r"c:\perflogs",
    r"c:\msocache",
]


# ------------------------------------------------------------------- утилиты

def human(n) -> str:
    """1234567 -> '1,18 МБ'."""
    if n is None:
        return "—"
    units = ["Б", "КБ", "МБ", "ГБ", "ТБ", "ПБ"]
    v = float(n)
    i = 0
    while v >= 1024.0 and i < len(units) - 1:
        v /= 1024.0
        i += 1
    if i == 0:
        return f"{int(v)} {units[i]}"
    txt = f"{v:.2f}" if v < 10 else (f"{v:.1f}" if v < 100 else f"{v:.0f}")
    return txt.replace(".", ",") + " " + units[i]


def human_int(n) -> str:
    return f"{n:,}".replace(",", " ")


def fmt_time(ts) -> str:
    try:
        return datetime.fromtimestamp(ts).strftime("%d.%m.%Y %H:%M")
    except (OSError, OverflowError, ValueError):
        return "—"


def get_drives():
    """[('C:\\\\', 'Локальный диск', 'Windows', free_bytes), ...]"""
    types = {0: "Неизвестный", 1: "Нет корня", 2: "Съёмный", 3: "Локальный",
             4: "Сетевой", 5: "CD/DVD", 6: "RAM-диск"}
    result = []
    try:
        mask = ctypes.windll.kernel32.GetLogicalDrives()
    except Exception:
        mask = 0
    for i in range(26):
        if not (mask & (1 << i)):
            continue
        letter = chr(ord("A") + i)
        root = f"{letter}:\\"
        if not os.path.exists(root):
            continue
        try:
            dtype = ctypes.windll.kernel32.GetDriveTypeW(ctypes.c_wchar_p(root))
        except Exception:
            dtype = 0
        if dtype not in (2, 3, 4, 6):
            continue
        label = ""
        try:
            buf = ctypes.create_unicode_buffer(261)
            fsbuf = ctypes.create_unicode_buffer(261)
            ok = ctypes.windll.kernel32.GetVolumeInformationW(
                ctypes.c_wchar_p(root), buf, 261, None, None, None, fsbuf, 261)
            if ok:
                label = buf.value
        except Exception:
            pass
        free = None
        try:
            free = shutil.disk_usage(root).free
        except OSError:
            pass
        result.append((root, types.get(dtype, "Диск"), label, free))
    return result


def is_reparse_point(entry) -> bool:
    try:
        st = entry.stat(follow_symlinks=False)
        return bool(getattr(st, "st_file_attributes", 0) & stat.FILE_ATTRIBUTE_REPARSE_POINT)
    except OSError:
        return True


def is_protected(path: str) -> bool:
    low = path.lower()
    if os.path.basename(low) in SYSTEM_FILES:
        return True
    return any(low.startswith(p + os.sep) or low == p for p in PROTECTED_DIRS)


def is_protected_folder(path: str) -> bool:
    """Папку нельзя удалять целиком: корень диска, системная папка, профиль пользователя."""
    low = os.path.normpath(path).lower()
    if len(low) <= 3:                                   # C:\ , D:\
        return True
    for p in PROTECTED_DIRS:
        if low == p or low.startswith(p + os.sep):
            return True
    try:
        home = os.path.normpath(os.path.expanduser("~")).lower()
        if home == low or home.startswith(low + os.sep):  # C:\, C:\Users, сам профиль
            return True
    except Exception:
        pass
    return False


def send_to_recycle_bin(paths) -> tuple[bool, str]:
    """Отправить файлы в Корзину через Shell API (операцию можно отменить)."""

    class SHFILEOPSTRUCTW(ctypes.Structure):
        _fields_ = [
            ("hwnd", ctypes.wintypes.HWND),
            ("wFunc", ctypes.wintypes.UINT),
            ("pFrom", ctypes.wintypes.LPCWSTR),
            ("pTo", ctypes.wintypes.LPCWSTR),
            ("fFlags", ctypes.c_uint16),
            ("fAnyOperationsAborted", ctypes.wintypes.BOOL),
            ("hNameMappings", ctypes.c_void_p),
            ("lpszProgressTitle", ctypes.wintypes.LPCWSTR),
        ]

    FO_DELETE = 3
    FOF_SILENT = 0x0004
    FOF_NOCONFIRMATION = 0x0010
    FOF_ALLOWUNDO = 0x0040
    FOF_NOCONFIRMMKDIR = 0x0200
    FOF_NOERRORUI = 0x0400

    flags = (FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT |
             FOF_NOERRORUI | FOF_NOCONFIRMMKDIR)

    shell = ctypes.windll.shell32
    shell.SHFileOperationW.argtypes = [ctypes.POINTER(SHFILEOPSTRUCTW)]
    shell.SHFileOperationW.restype = ctypes.c_int

    ok_all = True
    messages = []
    for start in range(0, len(paths), 200):
        chunk = [os.path.abspath(p) for p in paths[start:start + 200]]
        joined = "\0".join(chunk) + "\0\0"
        op = SHFILEOPSTRUCTW()
        op.hwnd = None
        op.wFunc = FO_DELETE
        op.pFrom = joined
        op.pTo = None
        op.fFlags = flags
        op.fAnyOperationsAborted = False
        op.hNameMappings = None
        op.lpszProgressTitle = None
        try:
            rc = shell.SHFileOperationW(ctypes.byref(op))
        except Exception as exc:  # pragma: no cover
            return False, f"Ошибка вызова Shell API: {exc}"
        if rc != 0:
            ok_all = False
            messages.append(f"код {rc}")
        if op.fAnyOperationsAborted:
            ok_all = False
            messages.append("операция прервана")
    return ok_all, "; ".join(dict.fromkeys(messages))


def reveal_in_explorer(path: str) -> None:
    try:
        subprocess.Popen(["explorer", f"/select,{os.path.normpath(path)}"])
    except Exception:
        pass


def open_file(path: str) -> None:
    try:
        os.startfile(path)  # type: ignore[attr-defined]
    except Exception:
        pass


def normalize_roots(roots):
    """Убрать вложенные и дублирующиеся корни. 'C:' -> 'C:\\'."""
    prepared = []
    for r in roots:
        p = os.path.abspath(r)
        if len(p) == 2 and p[1] == ":":
            p += os.sep                      # корень диска, а не текущая папка
        prepared.append(p)
    prepared = sorted(set(prepared), key=len)
    out = []
    for r in prepared:
        rl = r.lower()
        nested = False
        for o in out:
            ol = o.lower()
            prefix = ol if ol.endswith(os.sep) else ol + os.sep
            if rl == ol or rl.startswith(prefix):
                nested = True
                break
        if not nested:
            out.append(r)
    return out


# ------------------------------------------------------------------ сканер

class ScanResult:
    def __init__(self):
        self.rows = []
        self.files = 0
        self.dirs = 0
        self.bytes = 0
        self.errors = 0
        self.elapsed = 0.0
        self.cancelled = False


def scan(roots, min_size, max_results, skip_dirs, cancel_event, on_progress=None):
    """Рекурсивный обход корней. Возвращает ScanResult."""
    res = ScanResult()
    heap = []                                   # min-heap по размеру
    skip = {os.path.normpath(p).lower() for p in skip_dirs}
    started = time.time()
    last_report = 0.0
    current_dir = ""
    stack = list(roots)

    while stack:
        if cancel_event.is_set():
            res.cancelled = True
            break
        directory = stack.pop()
        current_dir = directory
        res.dirs += 1
        try:
            with os.scandir(directory) as it:
                for entry in it:
                    if cancel_event.is_set():
                        res.cancelled = True
                        break
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            p = entry.path
                            if os.path.normpath(p).lower() in skip:
                                continue
                            if is_reparse_point(entry):
                                continue          # junction / symlink — не обходим
                            stack.append(p)
                        elif entry.is_file(follow_symlinks=False):
                            st = entry.stat(follow_symlinks=False)
                            size = st.st_size
                            res.files += 1
                            res.bytes += size
                            if size >= min_size:
                                item = (size, entry.path)
                                if len(heap) < max_results:
                                    heapq.heappush(heap, item)
                                elif size > heap[0][0]:
                                    heapq.heapreplace(heap, item)
                    except OSError:
                        res.errors += 1
        except (PermissionError, OSError):
            res.errors += 1
        if on_progress:
            now = time.time()
            if now - last_report >= 0.12:
                last_report = now
                on_progress(res, current_dir, now - started)

    if on_progress:
        on_progress(res, current_dir, time.time() - started)

    for size, path in sorted(heap, key=lambda t: (-t[0], t[1].lower())):
        try:
            mtime = os.stat(path, follow_symlinks=False).st_mtime
        except OSError:
            mtime = 0
        folder, name = os.path.split(path)
        ext = os.path.splitext(name)[1].lower().lstrip(".")
        res.rows.append({
            "path": path,
            "size": size,
            "name": name,
            "folder": folder,
            "ext": ext.upper() if ext else "—",
            "mtime": mtime,
            "kind": "file",
            "protected": is_protected(path),
        })
    res.elapsed = time.time() - started
    return res


def _open_frame(stack, path, mtime, res):
    """Открыть кадр обхода папки (для подсчёта размеров снизу вверх)."""
    res.dirs += 1
    try:
        it = os.scandir(path)
    except (PermissionError, OSError):
        res.errors += 1
        it = None
    stack.append({"path": path, "it": it, "size": 0, "files": 0, "mtime": mtime})


def _close_frame(stack, frame, heap, min_size, max_results):
    """Закрыть кадр: положить папку в топ и прибавить её размер родителю."""
    it = frame["it"]
    if it is not None:
        try:
            it.close()
        except Exception:
            pass
        frame["it"] = None
    size = frame["size"]
    if size >= min_size:
        item = (size, frame["path"], frame["files"], frame["mtime"])
        if len(heap) < max_results:
            heapq.heappush(heap, item)
        elif size > heap[0][0]:
            heapq.heapreplace(heap, item)
    if stack:                                   # отдать сумму родительской папке
        stack[-1]["size"] += size
        stack[-1]["files"] += frame["files"]


def scan_folders(roots, min_size, max_results, skip_dirs, cancel_event, on_progress=None):
    """Обход с подсчётом суммарного размера каждой папки.

    Обход в глубину с пост-обработкой (post-order): память O(глубины дерева),
    а не O(числа папок), поэтому работает и на дисках с миллионами папок.
    """
    res = ScanResult()
    heap = []                                   # (размер, путь, файлов, mtime)
    skip = {os.path.normpath(p).lower() for p in skip_dirs}
    started = time.time()
    last_report = 0.0
    current_dir = ""

    for root_path in roots:
        try:
            mtime = os.stat(root_path, follow_symlinks=False).st_mtime
        except OSError:
            mtime = 0
        stack = []
        _open_frame(stack, root_path, mtime, res)

        while stack:
            if cancel_event.is_set():
                res.cancelled = True
                break
            frame = stack[-1]
            current_dir = frame["path"]
            it = frame["it"]
            if it is None:
                stack.pop()
                _close_frame(stack, frame, heap, min_size, max_results)
                continue
            try:
                entry = next(it)
            except StopIteration:
                stack.pop()
                _close_frame(stack, frame, heap, min_size, max_results)
                continue
            except OSError:
                res.errors += 1
                stack.pop()
                _close_frame(stack, frame, heap, min_size, max_results)
                continue
            try:
                if entry.is_dir(follow_symlinks=False):
                    p = entry.path
                    if os.path.normpath(p).lower() in skip:
                        continue
                    if is_reparse_point(entry):
                        continue
                    try:
                        child_mtime = entry.stat(follow_symlinks=False).st_mtime
                    except OSError:
                        child_mtime = 0
                    _open_frame(stack, p, child_mtime, res)
                elif entry.is_file(follow_symlinks=False):
                    st = entry.stat(follow_symlinks=False)
                    frame["size"] += st.st_size
                    frame["files"] += 1
                    res.files += 1
                    res.bytes += st.st_size
            except OSError:
                res.errors += 1
            if on_progress:
                now = time.time()
                if now - last_report >= 0.12:
                    last_report = now
                    on_progress(res, current_dir, now - started)

        while stack:                            # сбросить незакрытые кадры при отмене
            frame = stack.pop()
            it = frame["it"]
            if it is not None:
                try:
                    it.close()
                except Exception:
                    pass

    if on_progress:
        on_progress(res, current_dir, time.time() - started)

    for size, path, files, mtime in sorted(heap, key=lambda t: (-t[0], t[1].lower())):
        folder, name = os.path.split(path)
        if not name:                            # корень диска вида "C:\"
            folder, name = path, path
        res.rows.append({
            "path": path,
            "size": size,
            "name": name,
            "folder": folder,
            "files": files,
            "ext": human_int(files),
            "mtime": mtime,
            "kind": "dir",
            "protected": is_protected_folder(path),
        })
    res.elapsed = time.time() - started
    return res


# ------------------------------------------------------------- диалог удаления

class ConfirmDialog:
    """Модальное окно подтверждения: 'recycle' | 'permanent' | None."""

    def __init__(self, parent, count, total, protected_hint=False,
                 kind="file", files=0):
        import tkinter as tk
        from tkinter import ttk

        is_dir = (kind == "folder")
        self.result = None
        self.top = tk.Toplevel(parent)
        top = self.top
        top.title("Подтверждение удаления")
        top.configure(bg=BG)
        top.resizable(False, False)
        top.transient(parent)

        wrap = tk.Frame(top, bg=BG, padx=26, pady=22)
        wrap.pack(fill="both", expand=True)

        tk.Label(wrap, text=("Удалить выбранные папки?" if is_dir
                             else "Удалить выбранные файлы?"),
                 bg=BG, fg=FG, font=(FONT, 15, "bold")).pack(anchor="w")
        subtitle = (f"{human_int(count)} папок · {human(total)}" if is_dir
                    else f"{human_int(count)} файл(ов) · {human(total)}")
        if is_dir and files:
            subtitle += f"  ·  внутри {human_int(files)} файл(ов)"
        tk.Label(wrap, text=subtitle, bg=BG, fg=ACCENT,
                 font=(FONT, 12)).pack(anchor="w", pady=(6, 0))

        if is_dir:
            tk.Label(wrap, text="Папка удаляется целиком вместе со всем её содержимым.",
                     bg=BG, fg=DANGER2, font=(FONT, 10, "bold"),
                     wraplength=520, justify="left").pack(anchor="w", pady=(12, 0))

        info = ("Файлы будут перемещены в Корзину — их можно восстановить.\n"
                "Кнопка «Безвозвратно» удаляет файлы навсегда.")
        tk.Label(wrap, text=info, bg=BG, fg=MUTED, justify="left",
                 font=(FONT, 9)).pack(anchor="w", pady=(12, 0))

        if protected_hint:
            tk.Label(wrap, text="Защищённые системные файлы пропущены.",
                     bg=BG, fg=GOLD, font=(FONT, 9)).pack(anchor="w", pady=(6, 0))

        btns = tk.Frame(wrap, bg=BG)
        btns.pack(fill="x", pady=(20, 0))

        b_perm = ttk.Button(btns, text="Безвозвратно", style="GhostDanger.TButton",
                            command=lambda: self._done("permanent"))
        b_perm.pack(side="left")
        b_cancel = ttk.Button(btns, text="Отмена", style="Ghost.TButton",
                              command=lambda: self._done(None))
        b_cancel.pack(side="right")
        b_rec = ttk.Button(btns, text="В Корзину", style="Danger.TButton",
                           command=lambda: self._done("recycle"))
        b_rec.pack(side="right", padx=(0, 10))

        top.protocol("WM_DELETE_WINDOW", lambda: self._done(None))
        top.bind("<Escape>", lambda e: self._done(None))
        top.bind("<Return>", lambda e: self._done("recycle"))

        top.update_idletasks()
        px = parent.winfo_rootx() + (parent.winfo_width() - top.winfo_width()) // 2
        py = parent.winfo_rooty() + (parent.winfo_height() - top.winfo_height()) // 3
        top.geometry(f"+{max(px, 0)}+{max(py, 0)}")
        top.grab_set()
        b_rec.focus_set()

    def _done(self, value):
        self.result = value
        try:
            self.top.grab_release()
            self.top.destroy()
        except Exception:
            pass


# ------------------------------------------------------------------ приложение

class DiskCleanerApp:
    ZEBRA_EVEN = "even"
    ZEBRA_ODD = "odd"

    def __init__(self, root):
        import tkinter as tk
        from tkinter import ttk

        self.tk = tk
        self.ttk = ttk
        self.root = root
        self.rows = []                 # все найденные файлы
        self.checked = set()           # пути отмеченных файлов
        self.sort_col = "size"
        self.sort_desc = True
        self.mode = "files"          # "files" — крупнейшие файлы, "folders" — папки
        self.scan_thread = None
        self.cancel_event = threading.Event()
        self.msg_queue = queue.Queue()
        self.scanning = False
        self.last_result = None
        self.custom_roots = []
        self.export_dir = os.path.join(os.path.expanduser("~"), "Desktop")
        self._vis = None                # кэш отфильтрованных/отсортированных строк

        self._build_theme()
        self._build_ui()
        self._refresh_roots()
        self._poll_queue()
        self._update_counters()
        self._fit_window()
        self._dark_titlebar()

    # ---------------------------------------------------------- оформление

    def _build_theme(self):
        from tkinter import ttk
        style = ttk.Style(self.root)
        try:
            style.theme_use("clam")
        except Exception:
            pass

        style.configure(".", background=BG, foreground=FG, font=(FONT, 10))
        style.configure("TFrame", background=BG)
        style.configure("Panel.TFrame", background=PANEL)
        style.configure("Card.TFrame", background=CARD)
        style.configure("TLabel", background=BG, foreground=FG, font=(FONT, 10))
        style.configure("Muted.TLabel", background=BG, foreground=MUTED, font=(FONT, 9))
        style.configure("PanelMuted.TLabel", background=PANEL, foreground=MUTED, font=(FONT, 9))
        style.configure("Panel.TLabel", background=PANEL, foreground=FG, font=(FONT, 10))
        style.configure("Title.TLabel", background=BG, foreground="#ffffff",
                        font=(FONT, 17, "bold"))
        style.configure("Section.TLabel", background=PANEL, foreground=MUTED,
                        font=(FONT, 8, "bold"))
        style.configure("Stat.TLabel", background=PANEL, foreground=FG,
                        font=(FONT, 11, "bold"))
        style.configure("StatAccent.TLabel", background=PANEL, foreground=ACCENT,
                        font=(FONT, 11, "bold"))
        style.configure("StatDanger.TLabel", background=PANEL, foreground=DANGER2,
                        font=(FONT, 11, "bold"))
        style.configure("TSeparator", background=BORDER)

        style.configure("TButton", background=HOVER, foreground=FG, borderwidth=0,
                        focusthickness=0, relief="flat", padding=(13, 7), font=(FONT, 10))
        style.map("TButton",
                  background=[("pressed", "#242830"), ("active", "#3a4049"),
                              ("disabled", PANEL)],
                  foreground=[("disabled", "#5d6673")])

        style.configure("Ghost.TButton", background=BG, foreground=MUTED,
                        borderwidth=0, padding=(11, 7), font=(FONT, 10))
        style.map("Ghost.TButton",
                  background=[("active", "#242830"), ("disabled", BG)],
                  foreground=[("active", FG), ("disabled", "#4a515c")])

        style.configure("GhostDanger.TButton", background=BG, foreground=DANGER2,
                        borderwidth=0, padding=(11, 7), font=(FONT, 10))
        style.map("GhostDanger.TButton",
                  background=[("active", "#33211f"), ("disabled", BG)],
                  foreground=[("disabled", "#5d4a48")])

        style.configure("Accent.TButton", background=ACCENT, foreground="#0d1117",
                        borderwidth=0, padding=(15, 8), font=(FONT, 10, "bold"))
        style.map("Accent.TButton",
                  background=[("pressed", "#3a7fd5"), ("active", ACCENT2),
                              ("disabled", "#2b3a4d")],
                  foreground=[("disabled", "#5d6673")])

        style.configure("Danger.TButton", background=DANGER, foreground="#ffffff",
                        borderwidth=0, padding=(15, 8), font=(FONT, 10, "bold"))
        style.map("Danger.TButton",
                  background=[("pressed", "#c4453e"), ("active", DANGER2),
                              ("disabled", "#4a2c2a")],
                  foreground=[("disabled", "#7d6a68")])

        style.configure("TCheckbutton", background=PANEL, foreground=FG,
                        focuscolor=PANEL, font=(FONT, 9))
        style.map("TCheckbutton",
                  background=[("active", PANEL)],
                  indicatorcolor=[("selected", ACCENT), ("!selected", "#3a4049")],
                  foreground=[("disabled", "#5d6673")])

        style.configure("TEntry", fieldbackground="#171a20", foreground=FG,
                        insertcolor=FG, bordercolor=BORDER, lightcolor=BORDER,
                        darkcolor=BORDER, padding=6, relief="flat")
        style.map("TEntry", bordercolor=[("focus", ACCENT)])

        style.configure("TCombobox", fieldbackground="#171a20", background=HOVER,
                        foreground=FG, arrowcolor=MUTED, bordercolor=BORDER,
                        lightcolor=BORDER, darkcolor=BORDER, padding=5, relief="flat")
        style.map("TCombobox",
                  fieldbackground=[("readonly", "#171a20"), ("disabled", PANEL)],
                  foreground=[("disabled", "#5d6673")],
                  arrowcolor=[("active", FG)])
        self.root.option_add("*TCombobox*Listbox.background", PANEL)
        self.root.option_add("*TCombobox*Listbox.foreground", FG)
        self.root.option_add("*TCombobox*Listbox.selectBackground", ACCENT)
        self.root.option_add("*TCombobox*Listbox.selectForeground", "#0d1117")
        self.root.option_add("*TCombobox*Listbox.font", (FONT, 10))

        style.configure("Mode.TRadiobutton", background=PANEL, foreground=FG,
                        focuscolor=PANEL, font=(FONT, 10), padding=(2, 2))
        style.map("Mode.TRadiobutton",
                  background=[("active", PANEL)],
                  indicatorcolor=[("selected", ACCENT), ("!selected", "#3a4049")],
                  foreground=[("disabled", "#5d6673")])

        style.configure("TSpinbox", fieldbackground="#171a20", foreground=FG,
                        arrowcolor=MUTED, bordercolor=BORDER, background=HOVER,
                        lightcolor=BORDER, darkcolor=BORDER, padding=5, relief="flat")

        style.configure("Treeview", background=CARD, fieldbackground=CARD,
                        foreground=FG, borderwidth=0, relief="flat",
                        rowheight=27, font=(FONT, 10))
        style.map("Treeview",
                  background=[("selected", SELECT)],
                  foreground=[("selected", "#ffffff")])
        style.configure("Treeview.Heading", background=PANEL, foreground=MUTED,
                        relief="flat", borderwidth=0, padding=(8, 9),
                        font=(FONT, 9, "bold"))
        style.map("Treeview.Heading",
                  background=[("active", HOVER)],
                  foreground=[("active", FG)])

        style.configure("Horizontal.TProgressbar", background=ACCENT,
                        troughcolor="#12141a", bordercolor="#12141a",
                        lightcolor=ACCENT, darkcolor=ACCENT, thickness=6)
        style.configure("Vertical.TScrollbar", background="#3a4049",
                        troughcolor=BG, bordercolor=BG, arrowcolor=MUTED,
                        relief="flat", width=12)
        style.map("Vertical.TScrollbar", background=[("active", "#4a515c")])
        style.configure("Horizontal.TScrollbar", background="#3a4049",
                        troughcolor=BG, bordercolor=BG, arrowcolor=MUTED,
                        relief="flat")
        style.map("Horizontal.TScrollbar", background=[("active", "#4a515c")])

    # ------------------------------------------------------------- сборка UI

    def _build_ui(self):
        tk, ttk = self.tk, self.ttk
        root = self.root
        root.title(f"{APP_TITLE}  v{APP_VERSION}")
        root.configure(bg=BG)
        root.minsize(1000, 600)

        # ---------- шапка
        header = tk.Frame(root, bg=BG, padx=22, pady=16)
        header.pack(fill="x")
        left = tk.Frame(header, bg=BG)
        left.pack(side="left", fill="x", expand=True)
        tk.Label(left, text="Disk Cleaner", bg=BG, fg="#ffffff",
                 font=(FONT, 18, "bold")).pack(anchor="w")
        tk.Label(left, text="Поиск самых больших файлов на компьютере и очистка диска",
                 bg=BG, fg=MUTED, font=(FONT, 9)).pack(anchor="w", pady=(2, 0))

        self.drive_info = tk.Label(header, text="", bg=BG, fg=MUTED,
                                   font=(FONT, 9), justify="right")
        self.drive_info.pack(side="right")

        # ---------- панель настроек
        panel = tk.Frame(root, bg=PANEL, padx=18, pady=14)
        panel.pack(fill="x", padx=22)

        row1 = tk.Frame(panel, bg=PANEL)
        row1.pack(fill="x")

        tk.Label(row1, text="ГДЕ ИСКАТЬ", bg=PANEL, fg=MUTED,
                 font=(FONT, 8, "bold")).grid(row=0, column=0, sticky="w")
        self.root_combo = ttk.Combobox(row1, state="readonly", width=46,
                                       font=(FONT, 10))
        self.root_combo.grid(row=1, column=0, sticky="w", pady=(4, 0))
        self.root_combo.bind("<<ComboboxSelected>>", lambda e: self._refresh_roots())

        ttk.Button(row1, text="Добавить папку…", style="Ghost.TButton",
                   command=self._add_folder).grid(row=1, column=1, padx=(10, 0),
                                                  pady=(4, 0))
        ttk.Button(row1, text="Убрать", style="Ghost.TButton",
                   command=self._remove_folder).grid(row=1, column=2, padx=(6, 0),
                                                     pady=(4, 0))

        tk.Label(row1, text="МИН. РАЗМЕР, МБ", bg=PANEL, fg=MUTED,
                 font=(FONT, 8, "bold")).grid(row=0, column=3, sticky="w", padx=(24, 0))
        self.min_size_var = tk.StringVar(value="100")
        ttk.Spinbox(row1, from_=0, to=1048576, increment=50, width=10,
                    textvariable=self.min_size_var,
                    command=self._on_filter_change).grid(row=1, column=3, sticky="w",
                                                         padx=(24, 0), pady=(4, 0))

        tk.Label(row1, text="ПОКАЗАТЬ ТОП", bg=PANEL, fg=MUTED,
                 font=(FONT, 8, "bold")).grid(row=0, column=4, sticky="w", padx=(16, 0))
        self.top_n_var = tk.StringVar(value="500")
        ttk.Spinbox(row1, from_=10, to=200000, increment=100, width=10,
                    textvariable=self.top_n_var).grid(row=1, column=4, sticky="w",
                                                      padx=(16, 0), pady=(4, 0))

        self.skip_sys_var = tk.BooleanVar(value=True)
        ttk.Checkbutton(row1, text="Пропускать системные папки Windows",
                        variable=self.skip_sys_var).grid(row=1, column=5,
                                                         padx=(10, 0), pady=(4, 0))
        row1.columnconfigure(6, weight=1)

        row2 = tk.Frame(panel, bg=PANEL)
        row2.pack(fill="x", pady=(12, 0))

        self.btn_scan = ttk.Button(row2, text="Начать сканирование",
                                   style="Accent.TButton", command=self.start_scan)
        self.btn_scan.pack(side="left")
        self.btn_stop = ttk.Button(row2, text="Остановить", style="Ghost.TButton",
                                   command=self.stop_scan, state="disabled")
        self.btn_stop.pack(side="left", padx=(8, 0))

        tk.Label(row2, text="РЕЖИМ", bg=PANEL, fg=MUTED,
                 font=(FONT, 8, "bold")).pack(side="left", padx=(30, 10))
        self.mode_var = tk.StringVar(value="files")
        ttk.Radiobutton(row2, text="Крупнейшие файлы", value="files",
                        variable=self.mode_var, style="Mode.TRadiobutton",
                        command=self._on_mode_change).pack(side="left")
        ttk.Radiobutton(row2, text="Крупнейшие папки", value="folders",
                        variable=self.mode_var, style="Mode.TRadiobutton",
                        command=self._on_mode_change).pack(side="left", padx=(16, 0))

        row3 = tk.Frame(panel, bg=PANEL)
        row3.pack(fill="x", pady=(10, 0))
        tk.Label(row3, text="ПОИСК", bg=PANEL, fg=MUTED,
                 font=(FONT, 8, "bold")).pack(side="left")
        self.search_var = tk.StringVar()
        self.search_var.trace_add("write", lambda *_: self._on_filter_change())
        ttk.Entry(row3, textvariable=self.search_var, width=30).pack(side="left",
                                                                    padx=(8, 0))
        tk.Label(row3, text="по имени файла или папки", bg=PANEL, fg="#5d6673",
                 font=(FONT, 8)).pack(side="left", padx=(8, 0))
        ttk.Button(row3, text="Экспорт CSV", style="Ghost.TButton",
                   command=self.export_csv).pack(side="right")
        ttk.Button(row3, text="Снять все", style="Ghost.TButton",
                   command=self.uncheck_all).pack(side="right", padx=(0, 6))
        ttk.Button(row3, text="Отметить топ-10", style="Ghost.TButton",
                   command=lambda: self.check_top(10)).pack(side="right", padx=(0, 6))
        ttk.Button(row3, text="Отметить все", style="Ghost.TButton",
                   command=self.check_all).pack(side="right", padx=(0, 6))

        # ---------- прогресс
        prog = tk.Frame(root, bg=BG, padx=22, pady=10)
        prog.pack(fill="x")
        self.progress = ttk.Progressbar(prog, mode="indeterminate",
                                        style="Horizontal.TProgressbar")
        self.progress.pack(fill="x")
        self.progress_label = tk.Label(prog, text="Готово к сканированию",
                                       bg=BG, fg=MUTED, font=(FONT, 9), anchor="w")
        self.progress_label.pack(fill="x", pady=(6, 0))

        # ---------- нижняя панель (пакуется ДО таблицы, иначе Tk её обрежет)
        self.status = tk.Label(root, text="Готово", bg="#101216", fg=MUTED,
                               font=(FONT, 9), anchor="w", padx=18, pady=6)
        self.status.pack(fill="x", side="bottom")

        footer = tk.Frame(root, bg=PANEL, padx=18, pady=12)
        footer.pack(fill="x", side="bottom")

        self.cap_found, self.stat_found = self._stat_block(
            footer, "НАЙДЕНО ФАЙЛОВ", "0", "Stat.TLabel")
        self.cap_total, self.stat_total = self._stat_block(
            footer, "ОБЪЁМ НАЙДЕННОГО", "0 Б", "StatAccent.TLabel")
        self.cap_checked, self.stat_checked = self._stat_block(
            footer, "ОТМЕЧЕНО", "0 · 0 Б", "StatDanger.TLabel")
        self.cap_scan, self.stat_scan = self._stat_block(
            footer, "ПРОСКАНИРОВАНО", "—", "Stat.TLabel")

        right = tk.Frame(footer, bg=PANEL)
        right.pack(side="right")
        self.btn_delete = ttk.Button(right, text="Удалить отмеченные", style="Danger.TButton",
                                     command=self.delete_checked, state="disabled")
        self.btn_delete.pack(side="right")
        ttk.Button(right, text="Очистить список", style="Ghost.TButton",
                   command=self.clear_list).pack(side="right", padx=(0, 10))

        # ---------- таблица
        table_wrap = tk.Frame(root, bg=CARD)
        table_wrap.pack(fill="both", expand=True)

        cols = ("check", "size", "name", "folder", "ext", "mtime")
        self.tree = ttk.Treeview(table_wrap, columns=cols, show="headings",
                                 selectmode="extended")
        headings = {
            "check": "✓",
            "size": "Размер",
            "name": "Имя файла",
            "folder": "Папка",
            "ext": "Тип",
            "mtime": "Изменён",
        }
        widths = {"check": 46, "size": 105, "name": 300, "folder": 520,
                  "ext": 70, "mtime": 130}
        anchors = {"check": "center", "size": "e", "name": "w", "folder": "w",
                   "ext": "center", "mtime": "center"}
        for c in cols:
            self.tree.heading(c, text=headings[c],
                              command=lambda cc=c: self._sort_by(cc))
            self.tree.column(c, width=widths[c], anchor=anchors[c],
                             stretch=(c == "folder"))
        self.tree.tag_configure(self.ZEBRA_ODD, background=CARD2)
        self.tree.tag_configure(self.ZEBRA_EVEN, background=CARD)
        self.tree.tag_configure("protected", foreground=GOLD)
        self.tree.tag_configure("checked", background="#2a3b52")

        vsb = ttk.Scrollbar(table_wrap, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        self.tree.pack(side="left", fill="both", expand=True)

        self.tree.bind("<Button-1>", self._on_click)
        self.tree.bind("<Double-1>", self._on_double_click)
        self.tree.bind("<space>", self._on_space)
        self.tree.bind("<Button-3>", self._on_right_click)
        self.tree.bind("<Control-a>", lambda e: (self.check_all(), "break")[1])
        self.tree.bind("<Control-A>", lambda e: (self.check_all(), "break")[1])

        self.menu = tk.Menu(root, tearoff=0, bg=PANEL, fg=FG,
                            activebackground=ACCENT, activeforeground="#0d1117",
                            borderwidth=0, font=(FONT, 10))
        self.menu.add_command(label="Открыть расположение файла",
                              command=self._ctx_reveal)
        self.menu.add_command(label="Открыть файл", command=self._ctx_open)
        self.menu.add_separator()
        self.menu.add_command(label="Отметить / снять отметку", command=self._ctx_toggle)
        self.menu.add_command(label="Копировать путь", command=self._ctx_copy)
        self.menu.add_separator()
        self.menu.add_command(label="Удалить отмеченные…", command=self.delete_checked)

        self._refresh_drive_info()

    # ------------------------------------------------------------ режим

    def _on_mode_change(self):
        self.mode = self.mode_var.get()
        self.rows = []
        self.checked.clear()
        self._vis = None
        self.sort_col = "size"
        self.sort_desc = True
        self._rebuild_tree()
        folders = (self.mode == "folders")
        self.root.title(f"{APP_TITLE}  v{APP_VERSION}"
                        + ("  —  режим папок" if folders else ""))
        self.btn_delete.configure(text=("Удалить отмеченные папки" if folders
                                        else "Удалить отмеченные"))
        value = self.min_size_var.get().strip()
        if folders and value in ("100", ""):
            self.min_size_var.set("1024")
        elif not folders and value in ("1024", ""):
            self.min_size_var.set("100")
        if folders:
            self._set_status("Режим «Крупнейшие папки»: считается суммарный размер "
                             "каждой папки; удаление — целиком со всем содержимым.",
                             GOLD)
        else:
            self._set_status("Режим «Крупнейшие файлы».", MUTED)

    def _headings(self):
        if self.mode == "folders":
            return {"check": "✓", "size": "Размер", "name": "Папка",
                    "folder": "Родительская папка", "ext": "Файлов",
                    "mtime": "Изменён"}
        return {"check": "✓", "size": "Размер", "name": "Имя файла",
                "folder": "Папка", "ext": "Тип", "mtime": "Изменён"}

    def _fit_window(self):
        """Подогнать размер окна под содержимое (важно при масштабе 125–150 %)."""
        root = self.root
        try:
            root.update_idletasks()
            sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
            w = min(max(root.winfo_reqwidth() + 8, 1080), max(sw - 40, 820))
            h = min(max(root.winfo_reqheight() + 8, 640), max(sh - 80, 520))
            root.geometry(f"{w}x{h}+{max((sw - w) // 2, 0)}+{max((sh - h) // 3, 0)}")
        except Exception:
            root.geometry("1280x760")

    def _dark_titlebar(self):
        """Тёмный заголовок окна в Windows 10/11 (в тон интерфейсу)."""
        if sys.platform != "win32":
            return
        try:
            self.root.update_idletasks()
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())
            value = ctypes.c_int(1)
            for attr in (20, 19):
                if ctypes.windll.dwmapi.DwmSetWindowAttribute(
                        ctypes.c_void_p(hwnd), ctypes.c_uint(attr),
                        ctypes.byref(value), ctypes.sizeof(value)) == 0:
                    break
        except Exception:
            pass

    def _stat_block(self, parent, caption, value, style):
        tk = self.tk
        box = tk.Frame(parent, bg=PANEL)
        box.pack(side="left", padx=(0, 30))
        cap = tk.Label(box, text=caption, bg=PANEL, fg=MUTED, font=(FONT, 8, "bold"))
        cap.pack(anchor="w")
        lbl = self.ttk.Label(box, text=value, style=style)
        lbl.pack(anchor="w")
        return cap, lbl

    # -------------------------------------------------------------- диски

    def _refresh_drive_info(self):
        drives = get_drives()
        parts = []
        for root, kind, label, free in drives:
            name = label or kind
            free_txt = f", свободно {human(free)}" if free is not None else ""
            parts.append(f"{root.rstrip(chr(92))}  {name}{free_txt}")
        self.drive_info.configure(text="\n".join(parts) if parts else "Диски не найдены")

    def _refresh_roots(self):
        drives = get_drives()
        self.root_options = []
        if drives:
            self.root_options.append((f"Все диски ({len(drives)} шт.) — весь компьютер",
                                      [d[0] for d in drives]))
        for root, kind, label, free in drives:
            name = label or kind
            free_txt = f" · свободно {human(free)}" if free is not None else ""
            self.root_options.append((f"{root.rstrip(chr(92))}  —  {name}{free_txt}",
                                      [root]))
        for path in self.custom_roots:
            self.root_options.append((f"{path}  —  папка", [path]))

        values = [o[0] for o in self.root_options]
        self.root_combo.configure(values=values)
        if values and self.root_combo.current() < 0:
            self.root_combo.current(0)

    def _selected_roots(self):
        idx = self.root_combo.current()
        if idx < 0:
            return [d[0] for d in get_drives()]
        return list(self.root_options[idx][1])

    def _add_folder(self):
        from tkinter import filedialog
        path = filedialog.askdirectory(title="Выберите папку для сканирования")
        if not path:
            return
        path = os.path.abspath(path)
        if path not in self.custom_roots:
            self.custom_roots.append(path)
            self._refresh_roots()
            self.root_combo.current(len(self.root_combo["values"]) - 1)

    def _remove_folder(self):
        idx = self.root_combo.current()
        if idx < 0:
            return
        label, roots = self.root_options[idx]
        if len(roots) == 1 and roots[0] in self.custom_roots:
            self.custom_roots.remove(roots[0])
            self._refresh_roots()
            self.root_combo.current(0)
        else:
            self._set_status("Убрать можно только добавленные вручную папки.", GOLD)

    # ------------------------------------------------------------- сканирование

    def start_scan(self):
        if self.scanning:
            return
        roots = normalize_roots(self._selected_roots())
        if not roots:
            self._set_status("Не выбрано ни одного диска или папки.", DANGER2)
            return
        try:
            min_mb = max(0.0, float(self.min_size_var.get().replace(",", ".")))
        except ValueError:
            min_mb = 1024.0 if self.mode == "folders" else 100.0
            self.min_size_var.set("1024" if self.mode == "folders" else "100")
        try:
            top_n = max(1, int(float(self.top_n_var.get().replace(",", "."))))
        except ValueError:
            top_n = 500
            self.top_n_var.set("500")

        skip_dirs = SKIP_DIRS_DEFAULT if self.skip_sys_var.get() else []

        self.rows = []
        self.checked.clear()
        self._rebuild_tree()
        self.scanning = True
        self.cancel_event.clear()
        self.btn_scan.configure(state="disabled")
        self.btn_stop.configure(state="normal")
        self.btn_delete.configure(state="disabled")
        self.progress.configure(mode="indeterminate")
        self.progress.start(12)
        self._set_status(f"Сканирование: {', '.join(roots)}", ACCENT)

        args = (roots, int(min_mb * 1024 * 1024), top_n, skip_dirs,
                self.cancel_event, self._scan_progress)
        worker = self._scan_folders_worker if self.mode == "folders" else self._scan_worker
        self.scan_thread = threading.Thread(target=worker, args=args, daemon=True)
        self.scan_thread.start()

    def _scan_progress(self, res, current_dir, elapsed):
        self.msg_queue.put(("progress", (res.files, res.dirs, res.bytes,
                                         res.errors, current_dir, elapsed)))

    def _scan_worker(self, roots, min_size, top_n, skip_dirs, cancel_event, cb):
        try:
            result = scan(roots, min_size, top_n, skip_dirs, cancel_event, cb)
            self.msg_queue.put(("done", result))
        except Exception as exc:  # pragma: no cover
            self.msg_queue.put(("error", repr(exc)))

    def _scan_folders_worker(self, roots, min_size, top_n, skip_dirs, cancel_event, cb):
        try:
            result = scan_folders(roots, min_size, top_n, skip_dirs, cancel_event, cb)
            self.msg_queue.put(("done", result))
        except Exception as exc:  # pragma: no cover
            self.msg_queue.put(("error", repr(exc)))

    def stop_scan(self):
        if self.scanning:
            self.cancel_event.set()
            self._set_status("Останавливаю сканирование…", GOLD)

    def _poll_queue(self):
        try:
            while True:
                kind, payload = self.msg_queue.get_nowait()
                if kind == "progress":
                    files, dirs, nbytes, errors, current, elapsed = payload
                    path = current if len(current) <= 110 else "…" + current[-109:]
                    rate = files / elapsed if elapsed > 0.5 else 0
                    rate_txt = f"{rate:,.0f}".replace(",", " ")
                    self.progress_label.configure(
                        text=(f"Найдено файлов: {human_int(files)}   ·   "
                              f"Объём: {human(nbytes)}   ·   Папок: {human_int(dirs)}   ·   "
                              f"{rate_txt} файл/с   ·   Ошибок доступа: {errors}\n"
                              f"Сейчас: {path}"))
                    self.stat_scan.configure(text=f"{human_int(files)} · {human(nbytes)}")
                elif kind == "done":
                    self._scan_finished(payload)
                elif kind == "error":
                    self._scanning_off()
                    self._set_status(f"Ошибка сканирования: {payload}", DANGER2)
                elif kind == "delprogress":
                    done, total, name = payload
                    self.progress.configure(mode="determinate", maximum=max(total, 1))
                    self.progress["value"] = done
                    self.progress_label.configure(
                        text=f"Удаление {done} из {total}: {name}")
                elif kind == "deldone":
                    self._delete_finished(payload)
        except queue.Empty:
            pass
        self.root.after(100, self._poll_queue)

    def _scan_finished(self, result: ScanResult):
        self._scanning_off()
        self.last_result = result
        self.rows = result.rows
        self._rebuild_tree()
        word = "прервано" if result.cancelled else "завершено"
        self.progress_label.configure(
            text=(f"Сканирование {word} за {result.elapsed:.1f} с   ·   "
                  f"Проверено файлов: {human_int(result.files)} ({human(result.bytes)})   ·   "
                  f"Папок: {human_int(result.dirs)}   ·   Ошибок доступа: {result.errors}"))
        self.progress.stop()
        self.progress.configure(mode="determinate", value=0)
        self.stat_scan.configure(text=f"{human_int(result.files)} · {human(result.bytes)}")
        if self.rows:
            self._set_status(f"Найдено {human_int(len(self.rows))} "
                             f"{'папок' if self.mode == 'folders' else 'файлов'}. "
                             f"Отметьте ненужные и нажмите «Удалить отмеченные».",
                             OK)
        else:
            self._set_status(f"{'Папки' if self.mode == 'folders' else 'Файлы'} "
                             "подходящего размера не найдены. "
                             "Уменьшите минимальный размер.", GOLD)

    def _scanning_off(self):
        self.scanning = False
        self.progress.stop()
        self.btn_scan.configure(state="normal")
        self.btn_stop.configure(state="disabled")

    # ------------------------------------------------------------ таблица

    def _on_filter_change(self):
        if not self.scanning and self.rows:
            self._rebuild_tree()

    def _visible_rows(self):
        if self._vis is not None:
            return self._vis
        text = self.search_var.get().strip().lower() if hasattr(self, "search_var") else ""
        rows = self.rows
        if text:
            rows = [r for r in rows
                    if text in r["name"].lower() or text in r["folder"].lower()]
        keymap = {
            "size": lambda r: r["size"],
            "name": lambda r: r["name"].lower(),
            "folder": lambda r: r["folder"].lower(),
            "ext": lambda r: r["ext"].lower(),
            "mtime": lambda r: r["mtime"],
            "check": lambda r: (0 if r["path"] in self.checked else 1, -r["size"]),
        }
        if self.mode == "folders":              # колонка «Тип» показывает число файлов
            keymap["ext"] = lambda r: r.get("files", 0)
        key = keymap.get(self.sort_col, keymap["size"])
        self._vis = sorted(rows, key=key, reverse=self.sort_desc)
        return self._vis

    def _sort_by(self, col):
        if col == "check":
            return
        if self.sort_col == col:
            self.sort_desc = not self.sort_desc
        else:
            self.sort_col = col
            self.sort_desc = (col in ("size", "mtime"))
        self._rebuild_tree()

    def _rebuild_tree(self):
        self._vis = None
        self.tree.delete(*self.tree.get_children())
        rows = self._visible_rows()
        arrow = " ▼" if self.sort_desc else " ▲"
        base = self._headings()
        for c, t in base.items():
            self.tree.heading(c, text=(t + arrow) if c == self.sort_col else t)

        for i, r in enumerate(rows):
            checked = r["path"] in self.checked
            glyph = "🔒" if r["protected"] else ("☑" if checked else "☐")
            tags = []
            if checked:
                tags.append("checked")
            else:
                tags.append(self.ZEBRA_ODD if i % 2 else self.ZEBRA_EVEN)
            if r["protected"]:
                tags.append("protected")
            suffix = "   (системная)" if self.mode == "folders" else "   (системный)"
            name = r["name"] + (suffix if r["protected"] else "")
            self.tree.insert("", "end", iid=str(i),
                             values=(glyph, human(r["size"]), name, r["folder"],
                                     r["ext"], fmt_time(r["mtime"])),
                             tags=tuple(tags))
        self._update_counters()

    def _row_by_iid(self, iid):
        if not iid:
            return None
        try:
            return self._visible_rows()[int(iid)]
        except (ValueError, IndexError):
            return None

    def _on_click(self, event):
        region = self.tree.identify("region", event.x, event.y)
        if region != "cell":
            return None
        if self.tree.identify_column(event.x) != "#1":
            return None
        iid = self.tree.identify_row(event.y)
        if iid:
            self._toggle(iid)
        return "break"

    def _on_space(self, event):
        for iid in self.tree.selection():
            self._toggle(iid, silent=True)
        self._update_counters()
        return "break"

    def _toggle(self, iid, silent=False):
        row = self._row_by_iid(iid)
        if not row:
            return
        if row["protected"]:
            if not silent:
                self._set_status(f"Файл защищён от удаления: {row['name']}", GOLD)
            return
        path = row["path"]
        if path in self.checked:
            self.checked.discard(path)
        else:
            self.checked.add(path)
        checked = path in self.checked
        self.tree.set(iid, "check", "☑" if checked else "☐")
        idx = self.tree.index(iid)
        self.tree.item(iid, tags=(("checked",) if checked
                                  else ((self.ZEBRA_ODD if idx % 2 else self.ZEBRA_EVEN),)))
        self._update_counters()

    def check_all(self):
        for r in self._visible_rows():
            if not r["protected"]:
                self.checked.add(r["path"])
        self._rebuild_tree()

    def check_top(self, n):
        for r in self._visible_rows()[:n]:
            if not r["protected"]:
                self.checked.add(r["path"])
        self._rebuild_tree()

    def uncheck_all(self):
        self.checked.clear()
        self._rebuild_tree()

    def clear_list(self):
        self.rows = []
        self.checked.clear()
        self._rebuild_tree()
        self._set_status("Список очищен.", MUTED)

    def _net_total(self, rows):
        """Сумма размеров без двойного учёта вложенных папок."""
        if self.mode != "folders":
            return sum(r["size"] for r in rows)
        ordered = sorted(rows, key=lambda r: len(r["path"]))
        seen, total = [], 0
        for r in ordered:
            low = r["path"].lower().rstrip("\\/")
            if any(low.startswith(s + os.sep) for s in seen):
                continue
            seen.append(low)
            total += r["size"]
        return total

    def _update_counters(self):
        visible = self._visible_rows() if self.rows else []
        total = self._net_total(visible)
        checked = [r for r in self.rows if r["path"] in self.checked]
        csize = self._net_total(checked)
        folders = (self.mode == "folders")
        self.cap_found.configure(text="НАЙДЕНО ПАПОК" if folders else "НАЙДЕНО ФАЙЛОВ")
        self.cap_total.configure(text=("ОБЪЁМ БЕЗ ВЛОЖЕННЫХ" if folders
                                       else "ОБЪЁМ НАЙДЕННОГО"))
        self.stat_found.configure(text=human_int(len(visible)))
        self.stat_total.configure(text=human(total))
        self.stat_checked.configure(text=f"{human_int(len(checked))} · {human(csize)}")
        if self.scanning:
            self.btn_delete.configure(state="disabled")
        else:
            self.btn_delete.configure(state="normal" if checked else "disabled")

    # ------------------------------------------------------- контекстное меню

    def _ctx_target(self):
        sel = self.tree.selection()
        if sel:
            return self._row_by_iid(sel[0])
        return None

    def _on_right_click(self, event):
        iid = self.tree.identify_row(event.y)
        if iid:
            if iid not in self.tree.selection():
                self.tree.selection_set(iid)
            try:
                self.menu.tk_popup(event.x_root, event.y_root)
            finally:
                self.menu.grab_release()
        return "break"

    def _ctx_reveal(self):
        row = self._ctx_target()
        if row:
            reveal_in_explorer(row["path"])

    def _ctx_open(self):
        row = self._ctx_target()
        if row:
            open_file(row["path"])

    def _ctx_toggle(self):
        for iid in self.tree.selection():
            self._toggle(iid, silent=True)
        self._update_counters()

    def _ctx_copy(self):
        rows = [self._row_by_iid(i) for i in self.tree.selection()]
        text = "\n".join(r["path"] for r in rows if r)
        if text:
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            self._set_status("Пути скопированы в буфер обмена.", OK)

    def _on_double_click(self, event):
        iid = self.tree.identify_row(event.y)
        row = self._row_by_iid(iid)
        if row:
            reveal_in_explorer(row["path"])

    # ----------------------------------------------------------- удаление

    def delete_checked(self):
        if self.scanning:
            return
        folders = (self.mode == "folders")
        check = os.path.isdir if folders else os.path.isfile
        targets = [r for r in self.rows if r["path"] in self.checked]
        existing = [r for r in targets if check(r["path"])]
        if not existing:
            self._set_status("Не отмечено ни одного существующего объекта.", GOLD)
            return
        if folders:                             # не удаляем папку внутри удаляемой папки
            ordered = sorted(existing, key=lambda r: len(r["path"]))
            keep, seen = [], []
            for r in ordered:
                low = r["path"].lower().rstrip("\\/")
                if any(low.startswith(s + os.sep) for s in seen):
                    continue
                keep.append(r)
                seen.append(low)
            existing = keep
        total = sum(r["size"] for r in existing)
        inner = sum(r.get("files", 0) for r in existing) if folders else 0
        protected_skipped = any(r["protected"] for r in targets)

        dlg = ConfirmDialog(self.root, len(existing), total, protected_skipped,
                            kind=("folder" if folders else "file"), files=inner)
        self.root.wait_window(dlg.top)
        mode = dlg.result
        if not mode:
            return

        self.btn_delete.configure(state="disabled")
        self.btn_scan.configure(state="disabled")
        self.progress.configure(mode="determinate", maximum=len(existing), value=0)
        self._set_status("Удаление…", DANGER2)
        threading.Thread(target=self._delete_worker,
                         args=(existing, mode, self.mode), daemon=True).start()

    def _delete_worker(self, rows, mode, kind="files"):
        total = len(rows)
        deleted = []
        failed = []
        freed = 0
        errors = []

        if mode == "recycle":
            try:                            # Shell API требует инициализации COM
                ctypes.windll.ole32.CoInitialize(None)
            except Exception:
                pass
            paths = [r["path"] for r in rows]
            ok, msg = send_to_recycle_bin(paths)
            for i, r in enumerate(rows, 1):
                self.msg_queue.put(("delprogress", (i, total, r["name"])))
                if not os.path.exists(r["path"]):
                    deleted.append(r)
                    freed += r["size"]
                else:
                    failed.append(r)
            if failed and not ok:
                errors.append(msg or "Корзина недоступна")
            try:
                ctypes.windll.ole32.CoUninitialize()
            except Exception:
                pass
        else:
            for i, r in enumerate(rows, 1):
                self.msg_queue.put(("delprogress", (i, total, r["name"])))
                try:
                    freed_now = r["size"]
                    if kind == "folders":
                        shutil.rmtree(r["path"])
                    else:
                        os.remove(r["path"])
                    deleted.append(r)
                    freed += freed_now
                except OSError as exc:
                    failed.append(r)
                    errors.append(f"{os.path.basename(r['path'])}: {exc.strerror or exc}")

        self.msg_queue.put(("deldone", (deleted, failed, freed, errors, kind)))

    def _delete_finished(self, payload):
        deleted, failed, freed, errors, kind = payload
        if kind == "folders":                   # могли исчезнуть и вложенные папки
            self.rows = [r for r in self.rows if os.path.exists(r["path"])]
            self.checked = {p for p in self.checked if os.path.exists(p)}
        else:
            dead = {r["path"] for r in deleted}
            self.rows = [r for r in self.rows if r["path"] not in dead]
            self.checked -= dead
        self._rebuild_tree()
        self.progress.configure(value=0)
        self.btn_scan.configure(state="normal")

        word = "папок" if kind == "folders" else "файл(ов)"
        if failed and errors:
            self.progress_label.configure(
                text=f"Удалено {len(deleted)} {word}, освобождено {human(freed)}. "
                     f"Не удалось удалить {len(failed)}.")
            self._set_status(f"Не удалось удалить {len(failed)} {word}: "
                             f"{errors[0][:130]}", DANGER2)
        else:
            self.progress_label.configure(
                text=f"Удалено {len(deleted)} {word}. Освобождено {human(freed)}.")
            self._set_status(f"Готово: удалено {len(deleted)} {word}, "
                             f"освобождено {human(freed)}.", OK)
        self._refresh_drive_info()
        self._update_counters()

    # -------------------------------------------------------------- экспорт

    def export_csv(self):
        from tkinter import filedialog, messagebox
        if not self.rows:
            self._set_status("Список пуст — экспортировать нечего.", GOLD)
            return
        default = os.path.join(self.export_dir,
                               f"largest_files_{time.strftime('%Y%m%d_%H%M')}.csv")
        path = filedialog.asksaveasfilename(
            title="Сохранить список в CSV", defaultextension=".csv",
            initialfile=os.path.basename(default), initialdir=self.export_dir,
            filetypes=[("CSV", "*.csv"), ("Все файлы", "*.*")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                w = csv.writer(f, delimiter=";")
                folders = (self.mode == "folders")
                w.writerow(["Размер (байт)", "Размер",
                            "Папка" if folders else "Имя",
                            "Родительская папка" if folders else "Папка",
                            "Файлов" if folders else "Тип",
                            "Изменён", "Полный путь", "Отмечен",
                            "Системная" if folders else "Системный"])
                for r in self._visible_rows():
                    count = r.get("files", r["ext"]) if folders else r["ext"]
                    w.writerow([r["size"], human(r["size"]), r["name"], r["folder"],
                                count, fmt_time(r["mtime"]), r["path"],
                                "да" if r["path"] in self.checked else "нет",
                                "да" if r["protected"] else "нет"])
        except OSError as exc:
            messagebox.showerror("Ошибка", f"Не удалось сохранить файл:\n{exc}")
            return
        self._set_status(f"Список сохранён: {path}", OK)

    # -------------------------------------------------------------- прочее

    def _set_status(self, text, color=MUTED):
        self.status.configure(text=text, fg=color)


# ------------------------------------------------------------------- CLI-режим

def cli_main(argv):
    import argparse
    parser = argparse.ArgumentParser(description="Поиск самых больших файлов (консоль).")
    parser.add_argument("--cli", metavar="PATH", nargs="?", const="", default=None,
                        help="папка или диск для сканирования")
    parser.add_argument("--min-size-mb", type=float, default=100)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--all-drives", action="store_true")
    parser.add_argument("--folders", action="store_true",
                        help="искать крупнейшие папки, а не файлы")
    args = parser.parse_args(argv)

    if args.all_drives or args.cli == "":
        roots = [d[0] for d in get_drives()]
    else:
        roots = [args.cli]
    roots = normalize_roots(roots)

    cancel = threading.Event()
    print(f"Сканирование: {', '.join(roots)} | режим "
          f"{'папки' if args.folders else 'файлы'} | мин. размер "
          f"{args.min_size_mb:g} МБ | топ {args.top}")
    t0 = time.time()

    def progress(res, current, elapsed):
        sys.stdout.write(f"\r  файлов: {res.files:,}  папок: {res.dirs:,}  "
                         f"объём: {human(res.bytes)}  ошибок: {res.errors}   ")
        sys.stdout.flush()

    worker = scan_folders if args.folders else scan
    result = worker(roots, int(args.min_size_mb * 1024 * 1024), args.top, [],
                    cancel, progress)
    print(f"\nГотово за {time.time() - t0:.1f} с.\n")
    if args.folders:
        print(f"{'РАЗМЕР':>12} {'ФАЙЛОВ':>10}  ПАПКА")
    else:
        print(f"{'РАЗМЕР':>12}  ПУТЬ")
    print("-" * 100)
    for r in result.rows[:args.top]:
        mark = " [системная]" if r["protected"] else ""
        if args.folders:
            count = f"{r['files']:,}".replace(",", " ")
            print(f"{human(r['size']):>12} {count:>10}  {r['path']}{mark}")
        else:
            print(f"{human(r['size']):>12}  {r['path']}{mark}")
    print("-" * 100)
    print(f"Всего файлов: {result.files:,} | объём: {human(result.bytes)} | "
          f"папок: {result.dirs:,} | ошибок доступа: {result.errors}")
    return 0


def smoke_main():
    """Проверка, что GUI собирается без ошибок."""
    import tkinter as tk
    root = tk.Tk()
    app = DiskCleanerApp(root)
    root.after(1800, root.destroy)
    root.mainloop()
    print("GUI smoke test: OK")
    return 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)

    if sys.platform == "win32":
        try:
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            try:
                ctypes.windll.user32.SetProcessDPIAware()
            except Exception:
                pass

    if "--smoke" in argv:
        return smoke_main()
    if {"--cli", "--all-drives", "--folders", "-h", "--help"} & set(argv):
        return cli_main(argv)

    import tkinter as tk
    root = tk.Tk()
    DiskCleanerApp(root)
    root.mainloop()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
