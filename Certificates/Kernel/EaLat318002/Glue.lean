module

public import Certificates.Kernel.EaLat318002.All
public import Certificates.Kernel.EaLat318002.Wit
public import CFSG.Certificates.Kernel.EaLatGlue
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelEaLat318002

open Equiv CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat CFSG.KC.Misc.Clos

theorem ncw24_sound (x y : Perm (Fin 24)) (w : ℕ) (hw : w < 24)
    (h : ncw24 (pcode x) (pcode y) w = true) : x * y ≠ y * x := by
  intro hxy
  rw [ncw24, notB_iff, beq_iff] at h
  apply h
  have e1 := pcode_img (by norm_num) y ⟨w, hw⟩
  have e2 := pcode_img (by norm_num) x ⟨w, hw⟩
  have e3 := pcode_img (by norm_num) x (y ⟨w, hw⟩)
  have e4 := pcode_img (by norm_num) y (x ⟨w, hw⟩)
  have e5 : x (y ⟨w, hw⟩) = y (x ⟨w, hw⟩) := by
    rw [← Perm.mul_apply, hxy, Perm.mul_apply]
  change img (pcode x) (img (pcode y) (⟨w, hw⟩ : Fin 24)) =
    img (pcode y) (img (pcode x) (⟨w, hw⟩ : Fin 24))
  rw [e1, e2, e3, e4, e5]

theorem tag_all : ∀ e < 1024, TagOK (mul 24) (one 24) 191 V EC TG e := by
  intro e he
  have h := (list_all e he).2.2.2
  rw [tagAt, CFSG.KC.LQT.P.letB_eq, CFSG.KC.LQT.P.letB_eq] at h
  unfold TagOK
  cases ht : Nat.blt (TG e) 191
  · rw [ht] at h
    right
    rcases orB_iff.1 h with h | h
    · exact Or.inl (beq_iff.1 h)
    · exact Or.inr fun h' => (notB_iff.1 h) (beq_iff.2 h')
  · rw [ht] at h
    exact Or.inl ⟨blt_iff.1 ht, beq_iff.1 h⟩

theorem wit_prb : ∀ i < 191, ∀ j < i, bit (CM i) j = false → prb PR i j < 24 :=
  wit_all

end CertificateChecks.KernelEaLat318002

end
