module

public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.MaxD2.Basic

public section

namespace CertificateChecks.KernelLC.HePtW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermTool
open CertificateChecks.KernelLC.HeFix

@[expose] noncomputable def ptW (G : Nat → Nat) (wd : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun j _ acc => pg 14 (mask 14) (G j) acc) wd

theorem hsz : szOK 8330 14 = true := (CFSG.KS.MaxD2.band_e hid).1

theorem pg_wordTabK (G : Nat → Nat) :
    ∀ (wd : List Nat) {x : Nat}, x < 8330 → pg 14 (mask 14) (wordTabK 8330 14 G wd) x = ptW G wd x
  | [], x, hx => CFSG.KS.MaxD2.pidn_get hsz hx
  | j :: wd, x, hx => by
    change pg 14 (mask 14) (pcomp 8330 14 (mask 14) (G j) (wordTabK 8330 14 G wd)) x =
      pg 14 (mask 14) (G j) (ptW G wd x)
    rw [CFSG.KS.PF.pg_pcomp (by norm_num) hx, pg_wordTabK G wd hx]

theorem ptW_append (G : Nat → Nat) (l₁ l₂ : List Nat) (x : Nat) :
    ptW G (l₁ ++ l₂) x = ptW G l₁ (ptW G l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons j l ih =>
    change pg 14 (mask 14) (G j) (ptW G (l ++ l₂) x) = pg 14 (mask 14) (G j) (ptW G l (ptW G l₂ x))
    rw [ih]

theorem ptW_inv {G GI : Nat → Nat} :
    ∀ (wd : List Nat), (∀ j ∈ wd, ∀ x < 8330, pg 14 (mask 14) (G j) x < 8330 ∧
      pg 14 (mask 14) (GI j) (pg 14 (mask 14) (G j) x) = x) →
    ∀ x < 8330, ptW G wd x < 8330 ∧ ptW GI wd.reverse (ptW G wd x) = x
  | [], _, x, hx => ⟨hx, rfl⟩
  | j :: wd, h, x, hx => by
    obtain ⟨b, e⟩ := ptW_inv wd (fun i hi => h i (List.mem_cons_of_mem j hi)) x hx
    have hj := h j List.mem_cons_self _ b
    refine ⟨hj.1, ?_⟩
    rw [List.reverse_cons, ptW_append]
    change ptW GI wd.reverse (pg 14 (mask 14) (GI j) (pg 14 (mask 14) (G j) (ptW G wd x))) = x
    rw [hj.2, e]

theorem permOK_of {p q : Nat} (hp : cn p = true) (hq : cn q = true)
    (h : ∀ x < 8330, pg 14 (mask 14) q (pg 14 (mask 14) p x) = x) :
    permOK 8330 14 (mask 14) (8330 * 14) p q = true := by
  have hb := fun x (hx : x < 8330) => CFSG.KS.MaxD2.canon_lt hp hx
  unfold cn canonK at hp hq
  unfold permOK
  simp only [PK.bAnd_eq, Bool.and_eq_true] at hp hq ⊢
  refine ⟨hp.2.1, hq.2.1, PK.allN_iff.2 fun x hx => ?_⟩
  simp only [PK.strictB_eq, Bool.and_eq_true, Nat.blt_eq]
  exact ⟨hb x hx, by rw [h x hx]; exact Nat.beq_refl x⟩

end CertificateChecks.KernelLC.HePtW

end
