import time
import json
import winsound
import tkinter as tk
import tkinter.ttk as ttk
from tkinter import messagebox, simpledialog
from pathlib import Path
import mss
import numpy as np
import cv2
import pyautogui
import win32gui
import win32process
import win32con


class RegionSelector:
    """Tkinter ile tam ekran şeffaf overlay üzerinden bölge seçimi."""
    def __init__(self, parent, pid):
        self.parent = parent
        self.pid = pid
        self.selection = None
        self.top = None

        self.win_rect = self._get_window_rect_by_pid(pid)
        if not self.win_rect:
            messagebox.showerror("Hata", f"PID {pid} için pencere bulunamadı!")
            return

        self.win_left, self.win_top, self.win_right, self.win_bottom = self.win_rect
        self.win_w = self.win_right - self.win_left
        self.win_h = self.win_bottom - self.win_top

        self.top = tk.Toplevel(parent)
        self.top.attributes("-fullscreen", True)
        self.top.attributes("-alpha", 0.35)
        self.top.attributes("-topmost", True)
        self.top.config(bg="black", cursor="crosshair")
        self.top.overrideredirect(True)

        self.canvas = tk.Canvas(self.top, bg="black", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        self.screen_w = self.top.winfo_screenwidth()
        self.screen_h = self.top.winfo_screenheight()

        self.canvas.create_rectangle(
            self.win_left, self.win_top, self.win_right, self.win_bottom,
            outline="red", width=3
        )
        self.canvas.create_text(
            self.win_left + 10, self.win_top + 10,
            text=f"Hedef Pencere (PID {pid}) - Bu alan içinde seçim yapın",
            fill="red", anchor="nw", font=("Segoe UI", 12, "bold")
        )
        self.canvas.create_text(
            self.screen_w // 2, 40,
            text="Fare ile sol tıkla + sürükle → bölge seç  |  ESC = İptal",
            fill="yellow", font=("Segoe UI", 14, "bold")
        )

        self.start_x = None
        self.start_y = None
        self.rect_id = None

        self.canvas.bind("<ButtonPress-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.top.bind("<Escape>", lambda e: self.cancel())
        self.top.focus_force()

    def _get_window_rect_by_pid(self, pid):
        result = {}

        def enum_cb(hwnd, _):
            _, win_pid = win32process.GetWindowThreadProcessId(hwnd)
            if win_pid == pid and win32gui.IsWindowVisible(hwnd):
                rect = win32gui.GetWindowRect(hwnd)
                w = rect[2] - rect[0]
                h = rect[3] - rect[1]
                if w > 100 and h > 100:
                    if not result or (w * h > result["area"]):
                        result["rect"] = rect
                        result["area"] = w * h
            return True

        win32gui.EnumWindows(enum_cb, None)
        return result.get("rect")

    def on_press(self, event):
        self.start_x = event.x_root
        self.start_y = event.y_root
        if self.rect_id:
            self.canvas.delete(self.rect_id)

    def on_drag(self, event):
        if self.start_x is None:
            return
        if self.rect_id:
            self.canvas.delete(self.rect_id)
        self.rect_id = self.canvas.create_rectangle(
            self.start_x, self.start_y, event.x_root, event.y_root,
            outline="lime", width=2
        )

    def on_release(self, event):
        if self.start_x is None:
            return

        x1 = min(self.start_x, event.x_root)
        y1 = min(self.start_y, event.y_root)
        x2 = max(self.start_x, event.x_root)
        y2 = max(self.start_y, event.y_root)

        if x2 - x1 < 20 or y2 - y1 < 20:
            messagebox.showwarning("Uyarı", "Seçim çok küçük, tekrar deneyin.")
            return

        rel_x = (x1 - self.win_left) / self.win_w
        rel_y = (y1 - self.win_top) / self.win_h
        rel_w = (x2 - x1) / self.win_w
        rel_h = (y2 - y1) / self.win_h

        rel_x = max(0.0, min(1.0, rel_x))
        rel_y = max(0.0, min(1.0, rel_y))
        rel_w = max(0.01, min(1.0 - rel_x, rel_w))
        rel_h = max(0.01, min(1.0 - rel_y, rel_h))

        self.selection = {
            "rel_x": rel_x, "rel_y": rel_y,
            "rel_w": rel_w, "rel_h": rel_h,
            "abs": (x1, y1, x2, y2),
        }

        self.top.destroy()

    def cancel(self):
        self.selection = None
        if self.top:
            self.top.destroy()


class FishWatcherApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Metin2 Şablon Tabanlı Sohbet Okuyucu")
        self.root.geometry("420x640")
        self.root.attributes("-topmost", True)
        self.root.config(bg="#1e1e1e")

        self.is_running = False
        self.scan_interval = 1000
        self.target_pid = None
        self.selection = None

        # Şablon sistemi
        self.templates_dir = Path("templates")
        self.templates_dir.mkdir(exist_ok=True)
        self.templates_json = Path("templates.json")
        self.templates = self._load_templates()
        self.last_matched_template = None
        self.last_template_time = 0
        self.template_cooldown = 2.0

        # Valuable için zaman tabanlı debounce
        self.valuable_debounce = 2.0

        # Alarm / debounce
        self.alarm_active = False
        self.alarm_display_until = 0
        self.alarm_hold_time = 1.5
        self.valuable_seen = False

        # Debug: son eşleşme konumu
        self._last_match_loc = None

        # ---------- UI ----------
        tk.Label(root, text="Metin2 Şablon Okuyucu", bg="#1e1e1e", fg="#00ffcc",
                 font=("Segoe UI", 12, "bold")).pack(pady=8)

        # PID
        pid_frame = tk.Frame(root, bg="#1e1e1e")
        pid_frame.pack(pady=4)

        tk.Label(pid_frame, text="PID:", bg="#1e1e1e", fg="#dddddd",
                 font=("Segoe UI", 10)).pack(side="left", padx=4)

        self.pid_entry = tk.Entry(pid_frame, width=10, font=("Segoe UI", 10),
                                  bg="#2a2a2a", fg="#ffffff", insertbackground="white")
        self.pid_entry.pack(side="left", padx=4)

        tk.Button(pid_frame, text="PID Seç", bg="#007bff", fg="white",
                  font=("Segoe UI", 9, "bold"), command=self.pick_pid_by_click
                  ).pack(side="left", padx=4)

        # Tarama aralığı
        interval_frame = tk.Frame(root, bg="#1e1e1e")
        interval_frame.pack(pady=4)

        tk.Label(interval_frame, text="Tarama aralığı (ms):", bg="#1e1e1e",
                 fg="#dddddd", font=("Segoe UI", 9)).pack(side="left", padx=4)

        self.interval_var = tk.StringVar(value="1000")
        interval_combo = ttk.Combobox(interval_frame, textvariable=self.interval_var,
                                      values=["300", "500", "750", "1000", "1500", "2000"],
                                      width=6, state="readonly")
        interval_combo.pack(side="left", padx=4)
        interval_combo.bind("<<ComboboxSelected>>", self.update_interval)

        # Threshold
        thr_frame = tk.Frame(root, bg="#1e1e1e")
        thr_frame.pack(pady=2)

        tk.Label(thr_frame, text="Eşik (threshold):", bg="#1e1e1e",
                 fg="#dddddd", font=("Segoe UI", 9)).pack(side="left", padx=4)

        self.threshold_var = tk.StringVar(value="0.50")
        thr_combo = ttk.Combobox(thr_frame, textvariable=self.threshold_var,
                                 values=["0.20", "0.30", "0.40", "0.50", "0.60",
                                         "0.70", "0.80", "0.85"],
                                 width=6, state="readonly")
        thr_combo.pack(side="left", padx=4)

        # Bölge seç
        tk.Button(root, text="📐 Bölge Seç (Fare ile)", bg="#6f42c1", fg="white",
                  font=("Segoe UI", 10, "bold"), width=30,
                  command=self.select_region).pack(pady=8)

        # Seçim bilgisi
        self.selection_label = tk.Label(root, text="Bölge: Seçilmedi",
                                        bg="#1e1e1e", fg="#aaaaaa",
                                        font=("Segoe UI", 9))
        self.selection_label.pack(pady=2)

        # Şablon kaydet (kırpma destekli)
        tk.Button(root, text="📷 Şablon Kaydet (kırpma seçenekli)", bg="#fd7e14",
                  fg="white", font=("Segoe UI", 10, "bold"), width=30,
                  command=self.save_template_from_region).pack(pady=4)

        # Şablon listesi
        tmpl_frame = tk.Frame(root, bg="#1e1e1e")
        tmpl_frame.pack(pady=6, fill="x", padx=10)

        tk.Label(tmpl_frame, text="Kayıtlı Şablonlar:", bg="#1e1e1e", fg="#dddddd",
                 font=("Segoe UI", 9, "bold")).pack(anchor="w")

        listbox_frame = tk.Frame(tmpl_frame, bg="#1e1e1e")
        listbox_frame.pack(fill="x", pady=2)

        self.template_listbox = tk.Listbox(listbox_frame, height=6,
                                           bg="#2a2a2a", fg="#ffffff",
                                           selectbackground="#6f42c1",
                                           font=("Consolas", 9))
        self.template_listbox.pack(side="left", fill="both", expand=True)

        scrollbar = tk.Scrollbar(listbox_frame, orient="vertical",
                                 command=self.template_listbox.yview)
        scrollbar.pack(side="right", fill="y")
        self.template_listbox.config(yscrollcommand=scrollbar.set)

        btn_frame = tk.Frame(tmpl_frame, bg="#1e1e1e")
        btn_frame.pack(fill="x", pady=2)

        tk.Button(btn_frame, text="🗑 Seçileni Sil", bg="#dc3545", fg="white",
                  font=("Segoe UI", 8, "bold"),
                  command=self.delete_selected_template).pack(side="left", padx=2)
        tk.Button(btn_frame, text="🔄 Yenile", bg="#17a2b8", fg="white",
                  font=("Segoe UI", 8, "bold"),
                  command=self.refresh_template_list).pack(side="left", padx=2)

        # Durum
        self.status_label = tk.Label(root, text="Durum: Beklemede",
                                     bg="#1e1e1e", fg="#ff4444",
                                     font=("Segoe UI", 10, "bold"))
        self.status_label.pack(pady=6)

        # Başlat
        self.btn_toggle = tk.Button(root, text="BAŞLAT", bg="#28a745", fg="white",
                                    font=("Segoe UI", 11, "bold"), width=16,
                                    command=self.toggle_scan)
        self.btn_toggle.pack(pady=6)

        # Son eşleşme
        self.last_text_label = tk.Label(root, text="Son: -",
                                        bg="#1e1e1e", fg="#888888",
                                        font=("Consolas", 8), wraplength=390,
                                        justify="left")
        self.last_text_label.pack(pady=4)

        self.refresh_template_list()

    # ---------- Şablon Yönetimi ----------
    def _load_templates(self):
        if not self.templates_json.exists():
            return {}
        try:
            with open(self.templates_json, "r", encoding="utf-8") as f:
                data = json.load(f)
            for key in list(data.keys()):
                p = Path(data[key]["file"])
                if not p.exists():
                    print(f"[UYARI] Şablon dosyası bulunamadı: {p}")
                    del data[key]
                    continue
                # Çok yüksek threshold'ları makul seviyeye çek
                if data[key].get("threshold", 1.0) > 0.85:
                    data[key]["threshold"] = 0.50
            return data
        except Exception as e:
            print(f"templates.json okunamadı: {e}")
            return {}

    def _save_templates(self):
        try:
            with open(self.templates_json, "w", encoding="utf-8") as f:
                json.dump(self.templates, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"templates.json yazılamadı: {e}")

    def refresh_template_list(self):
        self.template_listbox.delete(0, tk.END)
        for key, info in self.templates.items():
            tip = info.get("type", "?")
            thr = info.get("threshold", 0.50)
            marker = "⭐" if tip == "valuable" else "➖"
            self.template_listbox.insert(
                tk.END, f"{marker} {key}  ({tip}, {thr:.2f})"
            )

    def delete_selected_template(self):
        sel = self.template_listbox.curselection()
        if not sel:
            messagebox.showwarning("Uyarı", "Silmek için bir şablon seçin.")
            return
        idx = sel[0]
        key = list(self.templates.keys())[idx]

        if not messagebox.askyesno("Sil", f"'{key}' şablonunu silmek istiyor musun?"):
            return

        info = self.templates.pop(key, None)
        if info:
            p = Path(info["file"])
            if p.exists():
                try:
                    p.unlink()
                except Exception as e:
                    print(f"Dosya silinemedi: {e}")
        self._save_templates()
        self.refresh_template_list()

    def update_interval(self, event=None):
        try:
            self.scan_interval = int(self.interval_var.get())
        except ValueError:
            self.scan_interval = 1000

    # ---------- Görüntü İşleme ----------
    def _preprocess(self, bgra_img):
        gray = cv2.cvtColor(bgra_img, cv2.COLOR_BGRA2GRAY)
        scale = 4 if gray.shape[0] < 150 else 3
        gray = cv2.resize(gray, None, fx=scale, fy=scale,
                          interpolation=cv2.INTER_LANCZOS4)
        gray = cv2.GaussianBlur(gray, (3, 3), 0)
        _, thresh = cv2.threshold(gray, 0, 255,
                                  cv2.THRESH_BINARY + cv2.THRESH_OTSU)
        if np.mean(thresh) < 127:
            thresh = cv2.bitwise_not(thresh)
        kernel = np.ones((2, 2), np.uint8)
        thresh = cv2.morphologyEx(thresh, cv2.MORPH_OPEN, kernel)
        return thresh

    def _grab_region(self, pid):
        rect = self._get_window_rect_by_pid(pid)
        if not rect:
            return None
        win_left, win_top, win_right, win_bottom = rect
        win_w = win_right - win_left
        win_h = win_bottom - win_top

        s = self.selection
        chat_region = {
            "left": win_left + int(win_w * s["rel_x"]),
            "top": win_top + int(win_h * s["rel_y"]),
            "width": max(1, int(win_w * s["rel_w"])),
            "height": max(1, int(win_h * s["rel_h"])),
        }
        with mss.MSS() as sct:
            img = np.array(sct.grab(chat_region))
        return img

    # ---------- Kırpma Aracı ----------
    def _show_crop_selector(self, processed_img):
        """İşlenmiş görüntüden fareyle bölge kırp. Kırpılmış görüntüyü döndür."""
        try:
            win_name = "KIRP - Surukle sec | ENTER onayla | ESC iptal"
            cv2.namedWindow(win_name, cv2.WINDOW_NORMAL)
            cv2.resizeWindow(win_name, processed_img.shape[1], processed_img.shape[0])
            cv2.moveWindow(win_name, 100, 100)

            roi = cv2.selectROI(win_name, processed_img,
                                showCrosshair=True, fromCenter=False)
            cv2.destroyWindow(win_name)

            x, y, w, h = roi
            if w < 5 or h < 5:
                return None

            cropped = processed_img[y:y+h, x:x+w].copy()
            return cropped
        except Exception as e:
            print(f"Kırpma hatası: {e}")
            try:
                cv2.destroyAllWindows()
            except Exception:
                pass
            return None

    # ---------- Şablon Kaydet ----------
    def save_template_from_region(self):
        if not self.selection:
            messagebox.showerror("Hata", "Önce bölge seçin.")
            return
        pid_text = self.pid_entry.get().strip()
        if not pid_text.isdigit():
            messagebox.showerror("Hata", "Önce PID girin.")
            return

        pid = int(pid_text)

        # Ekran görüntüsünü al
        self.root.withdraw()
        self.root.update()
        time.sleep(0.5)

        try:
            img = self._grab_region(pid)
            self.root.deiconify()
        except Exception as e:
            self.root.deiconify()
            messagebox.showerror("Hata", f"Ekran görüntüsü alınamadı: {e}")
            return

        if img is None:
            messagebox.showerror("Hata", "Pencere bulunamadı.")
            return

        # Ön işleme
        processed = self._preprocess(img)

        # Kırpma modu sor
        crop_mode = messagebox.askyesno(
            "Kırpma Modu",
            "Şablonu kırpmak ister misin?\n\n"
            "Evet: Sadece önemli kısmı (örn: 'Altın Sudak') kaydet\n"
            "         → keyword araması gibi çalışır\n\n"
            "Hayır: Tüm mesajı kaydet\n"
            "         → tam mesaj eşleşmesi"
        )

        if crop_mode:
            crop = self._show_crop_selector(processed)
            if crop is None:
                messagebox.showinfo("İptal", "Kırpma iptal edildi.")
                return
            if crop.shape[0] < 5 or crop.shape[1] < 5:
                messagebox.showerror("Hata", "Kırpılan bölge çok küçük.")
                return
            processed = crop
            print(f"[Kırpma] Yeni boyut: {processed.shape[1]}x{processed.shape[0]}")

        # Şablon adı
        name = simpledialog.askstring("Şablon Adı",
                                      "Şablon adı (örn: altin_sudak):")
        if not name:
            return
        name = name.strip().lower().replace(" ", "_")

        if name in self.templates:
            if not messagebox.askyesno("Üzerine Yaz",
                                       f"'{name}' zaten var. Üzerine yazılsın mı?"):
                return

        kw = simpledialog.askstring("Anahtar Kelimeler",
                                    "Virgülle ayır (örn: altin,sudak):")
        keywords = [k.strip().lower() for k in (kw or "").split(",") if k.strip()]

        tip = simpledialog.askstring("Mesaj Tipi",
                                     "'valuable' (değerli) veya 'junk' (çöp):",
                                     initialvalue="junk")
        tip = (tip or "junk").strip().lower()
        if tip not in ("valuable", "junk"):
            tip = "junk"

        display = simpledialog.askstring("Görünen Ad",
                                         "Alarmda görünecek ad:",
                                         initialvalue=name.replace("_", " ").title())
        if not display:
            display = name.replace("_", " ").title()

        # Kaydet
        template_path = self.templates_dir / f"{name}.png"
        cv2.imwrite(str(template_path), processed)

        self.templates[name] = {
            "file": str(template_path),
            "keywords": keywords,
            "type": tip,
            "display": display,
            "threshold": float(self.threshold_var.get())
        }
        self._save_templates()
        self.refresh_template_list()

        messagebox.showinfo("Kaydedildi",
                            f"Şablon kaydedildi: {template_path.name}\n"
                            f"Boyut: {processed.shape[1]}x{processed.shape[0]}\n"
                            f"Tip: {tip}\n"
                            f"Threshold: {self.threshold_var.get()}\n"
                            f"Toplam şablon: {len(self.templates)}")

    # ---------- Template Matching ----------
    def match_template(self, processed_img):
        if not self.templates:
            return None, 0.0

        best_key = None
        best_score = 0.0
        all_scores = {}

        for key, info in self.templates.items():
            try:
                tmpl = cv2.imread(info["file"], cv2.IMREAD_GRAYSCALE)
                if tmpl is None:
                    continue

                # Şablon hedef görüntüden büyükse atla
                if (tmpl.shape[0] > processed_img.shape[0] or
                        tmpl.shape[1] > processed_img.shape[1]):
                    print(f"  [{key}] şablon hedeften büyük, atlanıyor")
                    continue

                # Template matching — şablon kendi boyutunda aranıyor
                result = cv2.matchTemplate(processed_img, tmpl, cv2.TM_CCOEFF_NORMED)
                _, max_val, _, max_loc = cv2.minMaxLoc(result)
                all_scores[key] = max_val

                if max_val > best_score:
                    best_score = max_val
                    best_key = key
                    self._last_match_loc = (key, max_loc, tmpl.shape)
            except Exception as e:
                print(f"Template match hatası ({key}): {e}")
                continue

        # Debug: ilk 3 skoru yazdır
        if all_scores:
            sorted_scores = sorted(all_scores.items(), key=lambda x: -x[1])
            top3 = ", ".join(f"{k}={v:.3f}" for k, v in sorted_scores[:3])
            print(f"  Skorlar: {top3}")

        return best_key, best_score

    # ---------- PID Seçimi ----------
    def pick_pid_by_click(self):
        messagebox.showinfo("PID Seç", "3 saniye içinde Metin2 penceresine tıklayın...")
        self.root.after(3000, self._capture_pid)

    def _capture_pid(self):
        try:
            x, y = pyautogui.position()
            hwnd = win32gui.WindowFromPoint((x, y))
            root_hwnd = win32gui.GetAncestor(hwnd, win32con.GA_ROOT)
            _, pid = win32process.GetWindowThreadProcessId(root_hwnd)
            self.pid_entry.delete(0, tk.END)
            self.pid_entry.insert(0, str(pid))
            title = win32gui.GetWindowText(root_hwnd)
            messagebox.showinfo("PID Bulundu", f"PID: {pid}\nBaşlık: {title}")
        except Exception as e:
            messagebox.showerror("Hata", f"PID alınamadı: {e}")

    # ---------- Bölge Seçimi ----------
    def select_region(self):
        pid_text = self.pid_entry.get().strip()
        if not pid_text.isdigit():
            messagebox.showerror("Hata",
                                 "Önce geçerli bir PID girin veya 'PID Seç' butonunu kullanın.")
            return

        self.target_pid = int(pid_text)

        self.root.withdraw()
        self.root.update()
        time.sleep(0.3)

        selector = RegionSelector(self.root, self.target_pid)
        if selector.top is None:
            self.root.deiconify()
            return

        self.root.wait_window(selector.top)
        self.root.deiconify()

        if selector.selection:
            self.selection = selector.selection
            s = selector.selection
            self.selection_label.config(
                text=f"Bölge: x={s['rel_x']:.2f} y={s['rel_y']:.2f} "
                     f"w={s['rel_w']:.2f} h={s['rel_h']:.2f}"
            )
        else:
            self.selection_label.config(text="Bölge: Seçilmedi (iptal)")

    # ---------- Tarama ----------
    def toggle_scan(self):
        if not self.is_running:
            pid_text = self.pid_entry.get().strip()
            if not pid_text.isdigit():
                messagebox.showerror("Hata", "PID giriniz.")
                return
            if not self.selection:
                messagebox.showerror("Hata", "Önce bölge seçiniz.")
                return
            if not self.templates:
                messagebox.showerror("Hata",
                                     "Hiç şablon yok. Önce 'Şablon Kaydet' ile ekleyin.")
                return

            self.target_pid = int(pid_text)
            self.is_running = True
            self.last_matched_template = None
            self.last_template_time = 0
            self.alarm_active = False
            self.alarm_display_until = 0
            self.status_label.config(text="Durum: Taranıyor...", fg="#28a745")
            self.btn_toggle.config(text="DURDUR", bg="#dc3545")
            self.root.after(200, self.scan_screen)
        else:
            self.is_running = False
            self.alarm_active = False
            self.status_label.config(text="Durum: Beklemede", fg="#ff4444")
            self.btn_toggle.config(text="BAŞLAT", bg="#28a745")
            self.last_text_label.config(text="Son: -")

    def _get_window_rect_by_pid(self, pid):
        result = {}

        def enum_cb(hwnd, _):
            _, win_pid = win32process.GetWindowThreadProcessId(hwnd)
            if win_pid == pid and win32gui.IsWindowVisible(hwnd):
                rect = win32gui.GetWindowRect(hwnd)
                w = rect[2] - rect[0]
                h = rect[3] - rect[1]
                if w > 100 and h > 100:
                    if not result or (w * h > result["area"]):
                        result["rect"] = rect
                        result["area"] = w * h
            return True

        win32gui.EnumWindows(enum_cb, None)
        return result.get("rect")

    def scan_screen(self):
        if not self.is_running:
            return

        # Alarm göstergesi süresi dolduysa temizle
        if self.alarm_active and time.time() > self.alarm_display_until:
            self.alarm_active = False
            if self.is_running:
                self.status_label.config(text="Durum: Taranıyor...", fg="#28a745")
            self.last_text_label.config(text="Son: -")

        try:
            img = self._grab_region(self.target_pid)
            if img is None:
                print(f"PID {self.target_pid} penceresi bulunamadı!")
                self.root.after(2000, self.scan_screen)
                return

            cv2.imwrite("debug_chat.png", img)
            processed = self._preprocess(img)
            cv2.imwrite("debug_processed.png", processed)

            matched_key, score = self.match_template(processed)

            if matched_key:
                info = self.templates[matched_key]
                threshold = float(info.get("threshold", 0.50))
                print(f"[Template] {matched_key} (skor={score:.3f}, eşik={threshold})")

                now = time.time()

                if score >= threshold:
                    if info["type"] == "valuable":
                        # Zaman bazlı debounce
                        same_key = (matched_key == self.last_matched_template)
                        elapsed = now - self.last_template_time
                        within_debounce = elapsed < self.valuable_debounce

                        if same_key and within_debounce:
                            print(f"  ↳ Aynı valuable debounce'da "
                                  f"({elapsed:.1f}s < {self.valuable_debounce}s), atlanıyor")
                        else:
                            if same_key:
                                print(f"  ↳ Aynı valuable ama {elapsed:.1f}s geçti → YENİ ALARM")
                            else:
                                print(f"  ↳ Farklı valuable → YENİ ALARM")
                            self.last_matched_template = matched_key
                            self.last_template_time = now
                            self.trigger_alarm(
                                f"skor={score:.2f}",
                                info["display"]
                            )
                    elif info["type"] == "junk":
                        same_key = (matched_key == self.last_matched_template)
                        elapsed = now - self.last_template_time
                        within_cooldown = elapsed < self.template_cooldown

                        if same_key and within_cooldown:
                            print(f"  ↳ Junk cooldown'da "
                                  f"({elapsed:.1f}s < {self.template_cooldown}s), atlanıyor")
                        else:
                            self.last_matched_template = matched_key
                            self.last_template_time = now
                            print(f"  ↳ Değersiz ({info['display']}), ESC basılıyor...")
                            pyautogui.press('esc')
                            time.sleep(0.5)
                else:
                    print(f"  ↳ Skor eşiğin altında ({score:.3f} < {threshold})")
            else:
                print(f"[Template] eşleşme yok (en iyi skor={score:.3f})")
                # Ekranda tanıdık metin yok → hafızayı sıfırla
                if self.last_matched_template:
                    old = self.templates.get(self.last_matched_template)
                    if old and old.get("type") == "valuable":
                        print("  ↳ Valuable ekrandan kayboldu, hafıza sıfırlandı")
                self.last_matched_template = None

        except Exception as e:
            print(f"Hata: {e}")

        if self.is_running:
            self.root.after(self.scan_interval, self.scan_screen)

    def trigger_alarm(self, text_found, fish_name):
        """Alarm çal — AMA programı DURDURMA. UI'da geçici uyarı göster."""
        try:
            winsound.Beep(2500, 400)
        except Exception:
            pass

        self.alarm_active = True
        self.alarm_display_until = time.time() + self.alarm_hold_time

        self.status_label.config(
            text=f"⭐ VALUABLE: {fish_name}!",
            fg="#ffc107"
        )
        self.last_text_label.config(
            text=f"⭐ BULUNDU: {fish_name} ({text_found})"
        )

        print(f"  ⭐ ALARM: {fish_name} bulundu! (taramaya devam)")


if __name__ == "__main__":
    root = tk.Tk()
    app = FishWatcherApp(root)
    root.mainloop()