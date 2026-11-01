"""
Save Swapper
============
Load game saves by copying the contents of a stored folder over your game's
save folder. Control it with global hotkeys and/or your voice:

    Load active save   - paste the active save over the game folder
    Create new save    - store the current game saves as a brand-new save
                         (auto-named with the date/time; it becomes active)
    "load <save name>" - (voice only) load a specific save by saying its name.
                         Works for names made of letters only (no digits).

Profiles let you keep a separate game folder and separate saves for each game.
Hotkeys and all other settings are shared between profiles.

The active save is whichever save is selected (and starred) in the window.
Click the gear button (top left) for options: voice commands, muting sounds, etc.

Setup:
    pip install keyboard vosk sounddevice
    Download a Vosk model (e.g. "vosk-model-small-en-us-0.15") from
    https://alphacephei.com/vosk/models , unzip it, and either put the folder
    next to this script or pick it with the Browse button in the Options window.

Run:     python save_swapper.py
(On Linux, the 'keyboard' library needs root. On Windows, run normally;
 if hotkeys don't work while your game is focused, try "Run as administrator".)
"""

import json
import os
import queue
import re
import shutil
import sys
import threading
import time
import tkinter as tk
import uuid
from datetime import datetime
from tkinter import filedialog, messagebox, simpledialog, ttk

try:
    import keyboard
except ImportError:
    keyboard = None

try:
    import sounddevice as sd
    from vosk import KaldiRecognizer, Model, SetLogLevel

    SetLogLevel(-1)
    VOICE_AVAILABLE = True
except (ImportError, OSError):  # OSError: PortAudio library missing
    sd = None
    VOICE_AVAILABLE = False

FROZEN = getattr(sys, "frozen", False)  # True when running as a PyInstaller exe
# Where the user's data lives: next to the exe (or next to the script)
APP_DIR = os.path.dirname(sys.executable) if FROZEN else os.path.dirname(os.path.abspath(__file__))
# Where files bundled inside the exe get unpacked (only differs for --onefile)
BUNDLE_DIR = getattr(sys, "_MEIPASS", APP_DIR)
CONFIG_PATH = os.path.join(APP_DIR, "save_swapper_config.json")
SAVES_DIR = os.path.join(APP_DIR, "saves")  # saves/<profile id>/<save id>
OLD_SLOTS_DIR = os.path.join(APP_DIR, "slots")  # name used by earlier versions

SAMPLE_RATE = 16000
VOICE_COOLDOWN = 1.5  # seconds to ignore further commands after one fires

HOTKEY_ACTIONS = [
    ("load", "Load active save"),
    ("new", "Create new save"),
]

# 16x16 pixel-art cat used for the window icon
CAT_PALETTE = {
    "K": "#2a1e1e",  # outline
    "O": "#f09640",  # fur
    "W": "#fff5e6",  # cheeks / muzzle
    "P": "#ff96aa",  # nose / inner ears
    "G": "#5ac85a",  # eyes
}
CAT_PIXELS = [
    "................",
    ".KK..........KK.",
    ".KPK........KPK.",
    ".KPOK......KOPK.",
    ".KOOOKKKKKKOOOK.",
    ".KOOOOOOOOOOOOK.",
    ".KOOOOOOOOOOOOK.",
    ".KOOGGOOOOGGOOK.",
    ".KOOGKOOOOKGOOK.",
    ".KOOOOOOOOOOOOK.",
    ".KOWWOOPPOOWWOK.",
    ".KOWWWOKKOWWWOK.",
    ".KOOWWWWWWWWOOK.",
    "..KOOOOOOOOOOK..",
    "...KKKKKKKKKK...",
    "................",
]


def make_cat_icon():
    img = tk.PhotoImage(width=16, height=16)
    for y, row in enumerate(CAT_PIXELS):
        for x, ch in enumerate(row):
            if ch in CAT_PALETTE:
                img.put(CAT_PALETTE[ch], (x, y))
    return img.zoom(4, 4)  # 64x64


# ----------------------------------------------------------------------------
# File operations
# ----------------------------------------------------------------------------
def clear_folder_contents(folder):
    """Delete everything inside folder, but keep the folder itself."""
    for name in os.listdir(folder):
        path = os.path.join(folder, name)
        if os.path.isdir(path) and not os.path.islink(path):
            shutil.rmtree(path)
        else:
            os.remove(path)


def paste_over(src, dst, clean=False):
    """Copy the contents of src over dst (overwriting). If clean, wipe dst first."""
    os.makedirs(dst, exist_ok=True)
    if clean:
        clear_folder_contents(dst)
    shutil.copytree(src, dst, dirs_exist_ok=True)


def snapshot(src, dst):
    """Replace dst with an exact copy of src."""
    if os.path.exists(dst):
        shutil.rmtree(dst)
    shutil.copytree(src, dst)


def timestamp_name():
    return datetime.now().strftime("Save %Y-%m-%d %H:%M:%S")


# ----------------------------------------------------------------------------
# Voice helpers
# ----------------------------------------------------------------------------
def normalize_phrase(text):
    """Lowercase, letters and spaces only, single-spaced."""
    return " ".join(re.sub(r"[^a-z\s]", " ", text.lower()).split())


def list_input_devices():
    if sd is None:
        return []
    out = []
    try:
        for i, d in enumerate(sd.query_devices()):
            if d["max_input_channels"] > 0:
                out.append(f"{i}: {d['name']}")
    except Exception:
        pass
    return out


def device_from_label(label):
    """Turn a combobox label like '3: Microphone (USB)' into a device index (or None = default)."""
    if sd is None or not label or label == "(default)":
        return None
    try:
        idx = int(label.split(":", 1)[0])
        if sd.query_devices(idx)["max_input_channels"] > 0:
            return idx
    except Exception:
        pass
    return None


def default_model_path():
    """Find a Vosk model next to the exe/script, or bundled inside the exe."""
    for base in (APP_DIR, BUNDLE_DIR):
        try:
            for name in sorted(os.listdir(base)):
                full = os.path.join(base, name)
                if os.path.isdir(full) and (name.startswith("vosk-model") or name == "model"):
                    return full
        except OSError:
            pass
    return ""


# ----------------------------------------------------------------------------
# App
# ----------------------------------------------------------------------------
class SaveSwapper:
    def __init__(self, root):
        self.root = root
        root.title("Save Swapper")
        root.geometry("720x500")
        root.minsize(640, 420)
        self.icon_image = make_cat_icon()
        root.iconphoto(True, self.icon_image)

        self.config = {
            "profiles": [],
            "active_profile": "",
            "clean_before_load": False,
            "mute_sounds": False,
            "hotkeys": {a: "" for a, _ in HOTKEY_ACTIONS},
            "voice_enabled": False,
            "voice_model": "",
            "voice_device": "(default)",
            "voice_load_phrase": "load save",
            "voice_new_phrase": "new save",
            "voice_min_conf": 0.6,
        }
        self.hotkey_removers = []
        self.load_config()
        if not os.path.isdir(self.config["voice_model"] or ""):
            # Saved path is empty or stale (e.g. a temp folder from an earlier exe run)
            self.config["voice_model"] = default_model_path()

        # Voice runtime state
        self.voice_map = {}            # phrase -> (action, save_id)
        self.voice_min_conf = float(self.config["voice_min_conf"])
        self.voice_stop = None
        self.voice_thread = None
        self.vosk_model = None
        self.vosk_model_path = ""
        self.grammar_dirty = True

        # Tk variables (all created before the UI and the first refresh_tree)
        self.hotkeys_on = tk.BooleanVar(value=True)
        self.clean_var = tk.BooleanVar(value=self.config["clean_before_load"])
        self.mute_var = tk.BooleanVar(value=self.config["mute_sounds"])
        self.game_var = tk.StringVar(value=self.profile["game_folder"])
        self.status = tk.StringVar(value="Ready.")
        self.hotkey_vars = {
            a: tk.StringVar(value=self.config["hotkeys"].get(a) or "(not set)")
            for a, _ in HOTKEY_ACTIONS
        }
        self.voice_on = tk.BooleanVar(value=False)
        self.voice_model_var = tk.StringVar(value=self.config["voice_model"])
        self.voice_device_var = tk.StringVar(value=self.config["voice_device"])
        self.voice_load_var = tk.StringVar(value=self.config["voice_load_phrase"])
        self.voice_new_var = tk.StringVar(value=self.config["voice_new_phrase"])
        self.voice_conf_var = tk.DoubleVar(value=self.voice_min_conf)
        self.voice_heard = tk.StringVar(value="-")

        self.build_ui()
        self.build_options_window()
        self.refresh_profiles()
        self.refresh_tree()
        self.register_hotkeys()
        root.protocol("WM_DELETE_WINDOW", self.on_close)

        if keyboard is None:
            messagebox.showwarning(
                "Hotkeys unavailable",
                "The 'keyboard' package isn't installed, so hotkeys are disabled.\n\n"
                "Install it with:  pip install keyboard",
            )

        if self.config.get("voice_enabled") and VOICE_AVAILABLE and self.voice_model_var.get():
            self.voice_on.set(True)
            self.start_voice()

    # ------------------------------------------------- profile-aware helpers
    @property
    def profile(self):
        for p in self.config["profiles"]:
            if p["id"] == self.config["active_profile"]:
                return p
        return self.config["profiles"][0]

    @property
    def saves(self):
        return self.profile["saves"]

    @property
    def active_id(self):
        return self.profile.get("active_save", "")

    @active_id.setter
    def active_id(self, value):
        self.profile["active_save"] = value

    def profile_dir(self):
        return os.path.join(SAVES_DIR, self.profile["id"])

    def save_path(self, save):
        return os.path.join(self.profile_dir(), save["id"])

    def undo_dir(self):
        return os.path.join(self.profile_dir(), "_undo")

    # ---------------------------------------------------------------- config
    def load_config(self):
        data = {}
        if os.path.exists(CONFIG_PATH):
            try:
                with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                    data = json.load(f)
            except (OSError, json.JSONDecodeError):
                data = {}

        # Migrate from earlier versions that used "slot" naming
        if "slots" in data:
            data["saves"] = data.pop("slots")
        if "active_slot" in data:
            data["active_save"] = data.pop("active_slot")
        hk = data.pop("hotkeys", {})
        if "save" in hk and "new" not in hk:
            hk["new"] = hk["save"]

        self.config.update(data)
        self.config["hotkeys"].update({k: v for k, v in hk.items() if k in self.config["hotkeys"]})

        # Migrate from the single-game layout to profiles
        if not self.config.get("profiles"):
            profile = {
                "id": "default",
                "name": "Default",
                "game_folder": self.config.get("game_folder", ""),
                "saves": self.config.get("saves", []),
                "active_save": self.config.get("active_save", ""),
            }
            self.config["profiles"] = [profile]
            self.config["active_profile"] = "default"
            self.migrate_legacy_files(profile)
        for key in ("game_folder", "saves", "active_save"):
            self.config.pop(key, None)

        # Drop leftovers from the old per-slot hotkey format
        for p in self.config["profiles"]:
            for s in p["saves"]:
                s.pop("load_hotkey", None)
                s.pop("save_hotkey", None)

        ids = [p["id"] for p in self.config["profiles"]]
        if self.config["active_profile"] not in ids:
            self.config["active_profile"] = ids[0]

    def migrate_legacy_files(self, profile):
        """Move saves/<save id> and saves/_undo into saves/<profile id>/."""
        try:
            dest = os.path.join(SAVES_DIR, profile["id"])
            for s in profile["saves"]:
                src = os.path.join(SAVES_DIR, s["id"])
                if os.path.isdir(src):
                    os.makedirs(dest, exist_ok=True)
                    shutil.move(src, os.path.join(dest, s["id"]))
            old_undo = os.path.join(SAVES_DIR, "_undo")
            if os.path.isdir(old_undo):
                os.makedirs(dest, exist_ok=True)
                shutil.move(old_undo, os.path.join(dest, "_undo"))
        except OSError:
            pass

    def save_config(self):
        self.profile["game_folder"] = self.game_var.get()
        self.config["clean_before_load"] = self.clean_var.get()
        self.config["mute_sounds"] = self.mute_var.get()
        self.config["voice_enabled"] = self.voice_on.get()
        self.config["voice_model"] = self.voice_model_var.get()
        self.config["voice_device"] = self.voice_device_var.get()
        self.config["voice_load_phrase"] = self.voice_load_var.get()
        self.config["voice_new_phrase"] = self.voice_new_var.get()
        self.config["voice_min_conf"] = self.voice_min_conf
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(self.config, f, indent=2)

    # -------------------------------------------------------------------- UI
    def build_ui(self):
        # Top bar: options button, profile picker, hotkeys toggle
        bar = ttk.Frame(self.root, padding=(10, 10, 10, 0))
        bar.pack(fill="x")
        ttk.Button(bar, text="\u2699", width=3, command=self.show_options).pack(side="left")
        ttk.Label(bar, text="Profile:").pack(side="left", padx=(10, 4))
        self.profile_combo = ttk.Combobox(bar, state="readonly", width=22)
        self.profile_combo.pack(side="left")
        self.profile_combo.bind("<<ComboboxSelected>>", self.on_profile_selected)
        for text, cmd in [("New", self.new_profile), ("Rename", self.rename_profile),
                          ("Delete", self.delete_profile)]:
            ttk.Button(bar, text=text, width=8, command=cmd).pack(side="left", padx=(6, 0))
        ttk.Checkbutton(
            bar, text="Hotkeys enabled", variable=self.hotkeys_on, command=self.register_hotkeys
        ).pack(side="right")

        # Game folder (belongs to the current profile)
        top = ttk.Frame(self.root, padding=(10, 8, 10, 0))
        top.pack(fill="x")
        ttk.Label(top, text="Game save folder:").pack(side="left")
        ttk.Entry(top, textvariable=self.game_var).pack(side="left", fill="x", expand=True, padx=6)
        ttk.Button(top, text="Browse...", command=self.browse_game).pack(side="left")

        # Global hotkeys
        hk_frame = ttk.LabelFrame(self.root, text="Global hotkeys (work while your game is focused)", padding=8)
        hk_frame.pack(fill="x", padx=10, pady=(10, 0))
        for row, (action, label) in enumerate(HOTKEY_ACTIONS):
            ttk.Label(hk_frame, text=label + ":", width=22).grid(row=row, column=0, sticky="w", pady=2)
            ttk.Label(hk_frame, textvariable=self.hotkey_vars[action], width=22, relief="groove",
                      anchor="center").grid(row=row, column=1, padx=6, pady=2)
            ttk.Button(hk_frame, text="Set", width=8,
                       command=lambda a=action: self.set_hotkey(a)).grid(row=row, column=2, padx=2)
            ttk.Button(hk_frame, text="Clear", width=8,
                       command=lambda a=action: self.clear_hotkey(a)).grid(row=row, column=3, padx=2)

        # Saves
        mid = ttk.Frame(self.root, padding=10)
        mid.pack(fill="both", expand=True)

        self.tree = ttk.Treeview(mid, columns=("active", "name"), show="headings", selectmode="browse")
        self.tree.heading("active", text="Active")
        self.tree.heading("name", text="Save name")
        self.tree.column("active", width=60, anchor="center", stretch=False)
        self.tree.column("name", width=300)
        self.tree.pack(side="left", fill="both", expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.on_select)
        self.tree.bind("<Double-1>", lambda e: self.load_selected())
        sb = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        sb.pack(side="left", fill="y")
        self.tree.configure(yscrollcommand=sb.set)

        btns = ttk.Frame(mid, padding=(10, 0, 0, 0))
        btns.pack(side="left", fill="y")
        for text, cmd in [
            ("Load save", self.load_selected),
            ("Undo last load", self.undo_load),
            ("New save from game", self.new_save),
            ("Overwrite save", self.overwrite_selected),
            ("Rename", self.rename_selected),
            ("Move up", lambda: self.move_selected(-1)),
            ("Move down", lambda: self.move_selected(1)),
            ("Open saves folder", self.open_saves_folder),
            ("Delete save", self.delete_selected),
        ]:
            ttk.Button(btns, text=text, command=cmd, width=20).pack(pady=2)

        ttk.Label(self.root, textvariable=self.status, relief="sunken", anchor="w", padding=4).pack(
            fill="x", side="bottom"
        )

    def build_options_window(self):
        win = tk.Toplevel(self.root)
        win.title("Options")
        win.minsize(560, 0)
        win.withdraw()
        win.protocol("WM_DELETE_WINDOW", win.withdraw)
        self.options_win = win

        body = ttk.Frame(win, padding=10)
        body.pack(fill="both", expand=True)

        gen = ttk.LabelFrame(body, text="General", padding=8)
        gen.pack(fill="x")
        ttk.Checkbutton(
            gen, text="Mute the sound played when loading or creating saves",
            variable=self.mute_var, command=self.save_config,
        ).pack(anchor="w")
        ttk.Checkbutton(
            gen, text="Clean game folder before loading (removes files not in the save)",
            variable=self.clean_var, command=self.save_config,
        ).pack(anchor="w", pady=(4, 0))

        vf = ttk.LabelFrame(body, text="Voice commands", padding=8)
        vf.pack(fill="x", pady=(10, 0))
        vf.columnconfigure(1, weight=1)
        vf.columnconfigure(3, weight=1)

        ttk.Checkbutton(vf, text="Enable voice commands", variable=self.voice_on,
                        command=self.toggle_voice).grid(row=0, column=0, columnspan=2, sticky="w")
        ttk.Label(vf, text="Microphone:").grid(row=0, column=2, sticky="e", padx=(10, 4))
        self.device_combo = ttk.Combobox(
            vf, textvariable=self.voice_device_var, state="readonly",
            values=["(default)"] + list_input_devices(),
        )
        self.device_combo.grid(row=0, column=3, sticky="ew")
        self.device_combo.bind("<<ComboboxSelected>>", self.on_device_changed)

        ttk.Label(vf, text="Model folder:").grid(row=1, column=0, sticky="w", pady=(6, 0))
        ttk.Entry(vf, textvariable=self.voice_model_var).grid(row=1, column=1, columnspan=2, sticky="ew",
                                                              padx=(4, 4), pady=(6, 0))
        ttk.Button(vf, text="Browse...", command=self.browse_model).grid(row=1, column=3, sticky="w", pady=(6, 0))

        ttk.Label(vf, text="Load phrase:").grid(row=2, column=0, sticky="w", pady=(6, 0))
        e1 = ttk.Entry(vf, textvariable=self.voice_load_var)
        e1.grid(row=2, column=1, sticky="ew", padx=(4, 10), pady=(6, 0))
        ttk.Label(vf, text="New save phrase:").grid(row=2, column=2, sticky="e", pady=(6, 0))
        e2 = ttk.Entry(vf, textvariable=self.voice_new_var)
        e2.grid(row=2, column=3, sticky="ew", padx=(4, 0), pady=(6, 0))
        for e in (e1, e2):
            e.bind("<FocusOut>", self.voice_settings_changed)
            e.bind("<Return>", self.voice_settings_changed)

        ttk.Label(vf, text="Min. confidence:").grid(row=3, column=0, sticky="w", pady=(6, 0))
        spin = ttk.Spinbox(vf, from_=0.1, to=0.95, increment=0.05, width=6, textvariable=self.voice_conf_var,
                           command=self.voice_settings_changed)
        spin.grid(row=3, column=1, sticky="w", padx=(4, 0), pady=(6, 0))
        spin.bind("<FocusOut>", self.voice_settings_changed)
        ttk.Label(vf, text="Last heard:").grid(row=3, column=2, sticky="e", pady=(6, 0))
        ttk.Label(vf, textvariable=self.voice_heard).grid(row=3, column=3, sticky="w", padx=(4, 0), pady=(6, 0))

        hint = 'You can also say "load <save name>" for saves with letters-only names.'
        if not VOICE_AVAILABLE:
            hint = "Voice unavailable: run  pip install vosk sounddevice  and restart."
        ttk.Label(vf, text=hint, foreground="gray").grid(row=4, column=0, columnspan=4, sticky="w", pady=(6, 0))

        ttk.Button(body, text="Close", command=win.withdraw).pack(anchor="e", pady=(10, 0))

    def show_options(self):
        win = self.options_win
        win.geometry(f"+{self.root.winfo_rootx() + 30}+{self.root.winfo_rooty() + 30}")
        win.deiconify()
        win.lift()
        win.focus_force()

    def set_status(self, msg):
        self.status.set(msg)

    def ui(self, fn, *args):
        """Run fn on the Tk thread (safe to call from worker threads)."""
        self.root.after(0, fn, *args)

    def refresh_tree(self):
        self.tree.delete(*self.tree.get_children())
        for s in self.saves:
            mark = "\u2605" if s["id"] == self.active_id else ""
            self.tree.insert("", "end", iid=s["id"], values=(mark, s["name"]))
        active = self.active_id
        if active and self.tree.exists(active):
            self.tree.selection_set(active)
            self.tree.see(active)
        self.rebuild_voice_map()

    def update_markers(self):
        for s in self.saves:
            if self.tree.exists(s["id"]):
                mark = "\u2605" if s["id"] == self.active_id else ""
                self.tree.set(s["id"], "active", mark)

    def on_select(self, _event=None):
        sel = self.tree.selection()
        if sel and sel[0] != self.active_id:
            self.active_id = sel[0]
            self.save_config()
            self.update_markers()

    def selected_save(self):
        sel = self.tree.selection()
        if not sel:
            messagebox.showinfo("Save Swapper", "Select a save first.")
            return None
        return self.find_save(sel[0])

    def find_save(self, save_id):
        for s in self.saves:
            if s["id"] == save_id:
                return s
        return None

    # -------------------------------------------------------------- profiles
    def refresh_profiles(self):
        profiles = self.config["profiles"]
        self.profile_combo["values"] = [p["name"] for p in profiles]
        for i, p in enumerate(profiles):
            if p["id"] == self.config["active_profile"]:
                self.profile_combo.current(i)
                break

    def on_profile_selected(self, _event=None):
        idx = self.profile_combo.current()
        if 0 <= idx < len(self.config["profiles"]):
            target = self.config["profiles"][idx]
            if target["id"] != self.config["active_profile"]:
                self.switch_profile(target["id"])

    def switch_profile(self, profile_id):
        self.save_config()  # stores the game folder entry into the profile being left
        self.config["active_profile"] = profile_id
        self.game_var.set(self.profile["game_folder"])
        self.refresh_profiles()
        self.refresh_tree()
        self.save_config()
        self.set_status(f"Switched to profile '{self.profile['name']}'.")

    def profile_name_taken(self, name, ignore=None):
        return any(p["name"].lower() == name.lower() for p in self.config["profiles"] if p is not ignore)

    def new_profile(self):
        name = simpledialog.askstring("New profile", "Profile name (e.g. the game's name):", parent=self.root)
        if not name or not name.strip():
            return
        name = name.strip()
        if self.profile_name_taken(name):
            messagebox.showwarning("Save Swapper", f"A profile named '{name}' already exists.")
            return
        profile = {"id": uuid.uuid4().hex[:8], "name": name, "game_folder": "", "saves": [], "active_save": ""}
        self.config["profiles"].append(profile)
        self.switch_profile(profile["id"])
        self.browse_game()  # each game has its own save folder

    def rename_profile(self):
        profile = self.profile
        name = simpledialog.askstring("Rename profile", "New name:", initialvalue=profile["name"],
                                      parent=self.root)
        if not name or not name.strip():
            return
        name = name.strip()
        if self.profile_name_taken(name, ignore=profile):
            messagebox.showwarning("Save Swapper", f"A profile named '{name}' already exists.")
            return
        profile["name"] = name
        self.save_config()
        self.refresh_profiles()

    def delete_profile(self):
        if len(self.config["profiles"]) <= 1:
            messagebox.showinfo("Save Swapper", "You need at least one profile.")
            return
        profile = self.profile
        if not messagebox.askyesno(
            "Delete profile",
            f"Delete profile '{profile['name']}' and all {len(profile['saves'])} of its saves?\n\n"
            "This cannot be undone.",
        ):
            return
        shutil.rmtree(self.profile_dir(), ignore_errors=True)
        remaining = [p for p in self.config["profiles"] if p is not profile]
        self.config["profiles"] = remaining
        self.config["active_profile"] = remaining[0]["id"]
        self.game_var.set(remaining[0]["game_folder"])
        self.refresh_profiles()
        self.refresh_tree()
        self.save_config()
        self.set_status(f"Deleted profile '{profile['name']}'.")

    # ----------------------------------------------------------- game folder
    def browse_game(self):
        folder = filedialog.askdirectory(title=f"Select the save folder for '{self.profile['name']}'")
        if folder:
            self.game_var.set(folder)
            self.save_config()

    def game_folder(self, quiet=False):
        folder = self.game_var.get().strip()
        if not folder or not os.path.isdir(folder):
            if not quiet:
                messagebox.showerror("Save Swapper", "Set a valid game save folder first.")
            return None
        return folder

    # ----------------------------------------------------------------- saves
    def new_save(self):
        """Button: create a new save, asking for a name."""
        if not self.game_folder():
            return
        name = simpledialog.askstring(
            "New save", "Name for this save:", initialvalue=timestamp_name(), parent=self.root
        )
        if not name or not name.strip():
            return
        self.create_save(name.strip(), quiet=False)

    def create_save(self, name=None, quiet=True):
        """Store the current game folder as a brand-new save and make it active."""
        game = self.game_folder(quiet=quiet)
        if not game:
            self.set_status("New save failed: game folder not set.")
            return
        save = {"id": uuid.uuid4().hex[:10], "name": name or timestamp_name()}
        try:
            snapshot(game, self.save_path(save))
        except OSError as e:
            self.set_status(f"New save failed: {e}")
            if not quiet:
                messagebox.showerror("Save Swapper", f"Could not copy saves:\n{e}")
            return
        self.saves.append(save)
        self.active_id = save["id"]
        self.save_config()
        self.refresh_tree()
        self.set_status(f"Created '{save['name']}' (now active).")
        self.beep()

    def overwrite_selected(self):
        save = self.selected_save()
        if not save:
            return
        game = self.game_folder()
        if not game:
            return
        if not messagebox.askyesno(
            "Overwrite save", f"Replace '{save['name']}' with the current game saves?"
        ):
            return
        try:
            snapshot(game, self.save_path(save))
            self.set_status(f"Overwrote '{save['name']}'.")
            self.beep()
        except OSError as e:
            self.set_status(f"Overwrite failed: {e}")

    def load_selected(self):
        save = self.selected_save()
        if save:
            self.load_save(save["id"])

    def load_save(self, save_id):
        save = self.find_save(save_id)
        if not save:
            self.set_status("Load failed: no active save. Select or create a save first.")
            return
        game = self.game_folder(quiet=True)
        if not game:
            self.set_status("Load failed: game folder not set.")
            return
        src = self.save_path(save)
        if not os.path.isdir(src):
            self.set_status(f"Load failed: the stored folder for '{save['name']}' is missing.")
            return
        try:
            snapshot(game, self.undo_dir())  # safety copy so the load can be undone
            paste_over(src, game, clean=self.clean_var.get())
            self.set_status(f"Loaded '{save['name']}'.")
            self.beep()
        except OSError as e:
            self.set_status(f"Load failed (is the game still holding files open?): {e}")

    def undo_load(self):
        game = self.game_folder()
        if not game:
            return
        undo = self.undo_dir()
        if not os.path.isdir(undo):
            messagebox.showinfo("Save Swapper", "Nothing to undo yet.")
            return
        try:
            paste_over(undo, game, clean=True)
            self.set_status("Restored the saves from before the last load.")
            self.beep()
        except OSError as e:
            self.set_status(f"Undo failed: {e}")

    def rename_selected(self):
        save = self.selected_save()
        if not save:
            return
        name = simpledialog.askstring("Rename save", "New name:", initialvalue=save["name"], parent=self.root)
        if name and name.strip():
            save["name"] = name.strip()
            self.save_config()
            self.refresh_tree()

    def move_selected(self, step):
        save = self.selected_save()
        if not save:
            return
        saves = self.saves
        i = saves.index(save)
        j = i + step
        if 0 <= j < len(saves):
            saves[i], saves[j] = saves[j], saves[i]
            self.save_config()
            self.refresh_tree()

    def delete_selected(self):
        save = self.selected_save()
        if not save:
            return
        if not messagebox.askyesno("Delete save", f"Delete '{save['name']}' and its stored files?"):
            return
        shutil.rmtree(self.save_path(save), ignore_errors=True)
        self.saves.remove(save)
        if self.active_id == save["id"]:
            self.active_id = self.saves[0]["id"] if self.saves else ""
        self.save_config()
        self.refresh_tree()

    def open_saves_folder(self):
        folder = self.profile_dir()
        os.makedirs(folder, exist_ok=True)
        try:
            os.startfile(folder)  # Windows
        except AttributeError:
            import subprocess
            subprocess.Popen(["open" if sys.platform == "darwin" else "xdg-open", folder])

    # --------------------------------------------------------------- hotkeys
    def run_action(self, action):
        if action == "load":
            self.load_save(self.active_id)
        elif action == "new":
            self.create_save()

    def remove_hotkeys(self):
        """Remove only the hotkeys this app registered."""
        for remove in self.hotkey_removers:
            try:
                remove()
            except Exception:
                pass
        self.hotkey_removers = []

    def register_hotkeys(self):
        if keyboard is None:
            return
        self.remove_hotkeys()
        if not self.hotkeys_on.get():
            self.set_status("Hotkeys disabled.")
            return
        failed = []
        for action, _label in HOTKEY_ACTIONS:
            hk = self.config["hotkeys"].get(action, "")
            if not hk:
                continue
            try:
                remover = keyboard.add_hotkey(
                    hk, lambda a=action: self.root.after(0, self.run_action, a)
                )
                self.hotkey_removers.append(remover)
            except (ValueError, KeyError):
                failed.append(hk)
        if failed:
            self.set_status("Could not register: " + ", ".join(failed))

    def set_hotkey(self, action):
        if keyboard is None:
            messagebox.showerror("Save Swapper", "Install the 'keyboard' package: pip install keyboard")
            return
        label = dict(HOTKEY_ACTIONS)[action]

        self.remove_hotkeys()  # so existing hotkeys don't fire while capturing
        dlg = tk.Toplevel(self.root)
        dlg.title("Set hotkey")
        dlg.transient(self.root)
        dlg.grab_set()
        ttk.Label(
            dlg, padding=20,
            text=f"Press the key combination for\n'{label}'\n\n(Esc alone cancels)",
            justify="center",
        ).pack()

        def finish(hk):
            dlg.destroy()
            if hk and hk != "esc":
                clash = [
                    dict(HOTKEY_ACTIONS)[a] for a, v in self.config["hotkeys"].items()
                    if v == hk and a != action
                ]
                if clash:
                    messagebox.showwarning(
                        "Hotkey in use",
                        f"'{hk}' is already used for: {', '.join(clash)}.\nPick a different combination.",
                    )
                else:
                    self.config["hotkeys"][action] = hk
                    self.hotkey_vars[action].set(hk)
                    self.save_config()
            self.register_hotkeys()

        def worker():
            try:
                hk = keyboard.read_hotkey(suppress=False)
            except Exception:
                hk = None
            self.root.after(0, finish, hk)

        threading.Thread(target=worker, daemon=True).start()

    def clear_hotkey(self, action):
        self.config["hotkeys"][action] = ""
        self.hotkey_vars[action].set("(not set)")
        self.save_config()
        self.register_hotkeys()

    # ----------------------------------------------------------------- voice
    def browse_model(self):
        folder = filedialog.askdirectory(title="Select the unzipped Vosk model folder",
                                         parent=self.options_win)
        if folder:
            self.voice_model_var.set(folder)
            self.save_config()
            if self.voice_on.get():
                self.start_voice()

    def on_device_changed(self, _event=None):
        self.save_config()
        if self.voice_on.get():
            self.start_voice()

    def voice_settings_changed(self, _event=None):
        try:
            self.voice_min_conf = min(0.99, max(0.0, float(self.voice_conf_var.get())))
        except (tk.TclError, ValueError):
            self.voice_min_conf = 0.6
        self.save_config()
        self.rebuild_voice_map()

    def rebuild_voice_map(self):
        """Work out which spoken phrases map to which actions (current profile's saves only)."""
        mapping = {}
        for s in self.saves:
            if re.search(r"\d", s["name"]):
                continue  # names containing digits can't be spoken reliably
            name = normalize_phrase(s["name"])
            if name:
                mapping["load " + name] = ("load_id", s["id"])
        load_phrase = normalize_phrase(self.voice_load_var.get())
        new_phrase = normalize_phrase(self.voice_new_var.get())
        if load_phrase:
            mapping[load_phrase] = ("load", None)
        if new_phrase:
            mapping[new_phrase] = ("new", None)
        self.voice_map = mapping
        self.grammar_dirty = True

    def toggle_voice(self):
        self.save_config()
        if self.voice_on.get():
            self.start_voice()
        else:
            self.stop_voice()
            self.set_status("Voice commands off.")

    def start_voice(self):
        self.stop_voice()
        if not VOICE_AVAILABLE:
            messagebox.showerror(
                "Voice unavailable",
                "Install the voice packages first:\n\n    pip install vosk sounddevice\n\nThen restart the program.",
            )
            self.voice_on.set(False)
            return
        model_path = self.voice_model_var.get().strip()
        if not model_path or not os.path.isdir(model_path):
            messagebox.showerror(
                "Voice model needed",
                "Pick the folder of an unzipped Vosk model with the Browse button.\n\n"
                "Download one (e.g. vosk-model-small-en-us-0.15) from\nhttps://alphacephei.com/vosk/models",
            )
            self.voice_on.set(False)
            return
        self.voice_stop = threading.Event()
        device = device_from_label(self.voice_device_var.get())
        self.voice_thread = threading.Thread(
            target=self.voice_worker, args=(self.voice_stop, model_path, device), daemon=True
        )
        self.voice_thread.start()

    def stop_voice(self):
        if self.voice_stop is not None:
            self.voice_stop.set()
        self.voice_stop = None
        self.voice_thread = None

    def voice_failed(self, message):
        self.stop_voice()
        self.voice_on.set(False)
        self.save_config()
        self.set_status("Voice stopped: " + message)
        messagebox.showerror("Voice error", message)

    def make_recognizer(self):
        phrases = list(self.voice_map.keys()) + ["[unk]"]
        rec = KaldiRecognizer(self.vosk_model, SAMPLE_RATE, json.dumps(phrases))
        rec.SetWords(True)
        return rec

    def voice_worker(self, stop_event, model_path, device):
        """Runs in a background thread: mic -> Vosk -> commands."""
        try:
            if self.vosk_model is None or self.vosk_model_path != model_path:
                self.ui(self.set_status, "Loading voice model...")
                self.vosk_model = Model(model_path)
                self.vosk_model_path = model_path

            audio_q = queue.Queue()

            def callback(indata, frames, time_info, status):
                audio_q.put(bytes(indata))

            self.grammar_dirty = False
            rec = self.make_recognizer()
            last_fired = 0.0

            with sd.RawInputStream(samplerate=SAMPLE_RATE, blocksize=4000, device=device,
                                   dtype="int16", channels=1, callback=callback):
                self.ui(self.set_status, "Listening for voice commands...")
                while not stop_event.is_set():
                    if self.grammar_dirty:
                        self.grammar_dirty = False
                        rec = self.make_recognizer()
                    try:
                        data = audio_q.get(timeout=0.2)
                    except queue.Empty:
                        continue
                    if rec.AcceptWaveform(data):
                        result = json.loads(rec.Result())
                        last_fired = self.handle_voice_result(result, last_fired)
        except Exception as e:
            msg = str(e) or e.__class__.__name__
            if not stop_event.is_set():
                self.ui(self.voice_failed, msg)

    def handle_voice_result(self, result, last_fired):
        text = result.get("text", "").strip()
        if not text or text == "[unk]":
            return last_fired
        words = result.get("result") or []
        confs = [w.get("conf", 1.0) for w in words]
        conf = sum(confs) / len(confs) if confs else 1.0

        command = self.voice_map.get(text)
        now = time.time()
        if command and conf >= self.voice_min_conf and now - last_fired > VOICE_COOLDOWN:
            self.ui(self.voice_heard.set, f'"{text}" ({conf:.2f})')
            self.ui(self.run_voice_action, command[0], command[1])
            return now
        suffix = " - ignored" if command else " - no match"
        self.ui(self.voice_heard.set, f'"{text}" ({conf:.2f}){suffix}')
        return last_fired

    def run_voice_action(self, kind, save_id):
        if kind == "load":
            self.load_save(self.active_id)
        elif kind == "new":
            self.create_save()
        elif kind == "load_id" and self.find_save(save_id):
            self.active_id = save_id
            self.save_config()
            if self.tree.exists(save_id):
                self.tree.selection_set(save_id)
                self.tree.see(save_id)
            self.update_markers()
            self.load_save(save_id)

    # ----------------------------------------------------------------- misc
    def beep(self):
        if self.mute_var.get():
            return
        try:
            import winsound
            winsound.MessageBeep()
        except ImportError:
            self.root.bell()

    def on_close(self):
        self.stop_voice()
        self.save_config()
        self.root.destroy()


def main():
    # Migrate the folder name used by earlier versions ("slots" -> "saves")
    if os.path.isdir(OLD_SLOTS_DIR) and not os.path.exists(SAVES_DIR):
        os.rename(OLD_SLOTS_DIR, SAVES_DIR)
    os.makedirs(SAVES_DIR, exist_ok=True)

    root = tk.Tk()
    SaveSwapper(root)
    root.mainloop()


if __name__ == "__main__":
    main()
