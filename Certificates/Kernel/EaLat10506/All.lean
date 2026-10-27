module

public import Certificates.Kernel.EaLat10506.Checks
import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelEaLat10506

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

theorem slices_e : ∀ k < 8, ch10506e k = true := by
  intro k hk
  interval_cases k
  exacts [ch10506e0, ch10506e1, ch10506e2, ch10506e3, ch10506e4, ch10506e5, ch10506e6,
    ch10506e7]

theorem slices_u : ∀ k < 12, ch10506u k = true := by
  intro k hk
  interval_cases k
  exacts [ch10506u0, ch10506u1, ch10506u2, ch10506u3, ch10506u4, ch10506u5, ch10506u6,
    ch10506u7, ch10506u8, ch10506u9, ch10506u10, ch10506u11]

theorem slices_g : ∀ k < 27, ch10506g k = true := by
  intro k hk
  interval_cases k
  exacts [ch10506g0, ch10506g1, ch10506g2, ch10506g3, ch10506g4, ch10506g5, ch10506g6,
    ch10506g7, ch10506g8, ch10506g9, ch10506g10, ch10506g11, ch10506g12, ch10506g13,
    ch10506g14, ch10506g15, ch10506g16, ch10506g17, ch10506g18, ch10506g19, ch10506g20,
    ch10506g21, ch10506g22, ch10506g23, ch10506g24, ch10506g25, ch10506g26]

theorem list_all : ∀ e < 1024,
    CFSG.KC.Misc.Clos.treeAt M10 one10 GT 4 EC PA e = true ∧
      CFSG.KC.Misc.Clos.sortAt 1024 EC SG e = true ∧
      CFSG.KC.Misc.Clos.closedAt M10 GT 4 1024 EC CT e = true ∧ tagAt one10 e = true := by
  intro e he
  have h := slices_e (e / 128) (by omega)
  rw [ch10506e, letB_eq, allN_iff] at h
  have h2 := h (e % 128) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.mul 128 (e / 128)) (e % 128) = e by
    change 128 * (e / 128) + e % 128 = e
    omega] at h2
  obtain ⟨h3, h4⟩ := andB_iff.1 h2
  obtain ⟨h5, h6⟩ := andB_iff.1 h4
  obtain ⟨h7, h8⟩ := andB_iff.1 h6
  exact ⟨h3, h5, h7, h8⟩

theorem uni_fx_all : ∀ i < 191,
    uniAt M10 one10 191 V CM PR ncw11 i = true ∧ fxAt FX V i = true := by
  intro i hi
  have h := slices_u (i / 16) (by omega)
  rw [ch10506u, letB_eq, allN_iff] at h
  have h2 := h (i % 16) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.mul 16 (i / 16)) (i % 16) = i by
    change 16 * (i / 16) + i % 16 = i
    omega, impB_iff] at h2
  exact andB_iff.1 (h2 (blt_iff.2 hi))

theorem uni_all : ∀ i < 191, uniAt M10 one10 191 V CM PR ncw11 i = true :=
  fun i hi => (uni_fx_all i hi).1

theorem fx_all : ∀ i < 191, fxAt FX V i = true :=
  fun i hi => (uni_fx_all i hi).2

theorem base_ok : baseOK 191 REC = true := (andB_iff.1 ch10506z_ok).1

theorem gen_cov_fv_all : ∀ f, 0 < f → f < 7507 →
    genAt 191 REC CM PR f = true ∧ covAt 7507 REC CH f = true ∧ fvAt FV FX REC f = true := by
  intro f hf0 hf
  have h := slices_g ((f - 1) / 278) (by omega)
  rw [ch10506g, allN_iff] at h
  have h2 := h ((f - 1) % 278) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.add 1 (Nat.mul 278 ((f - 1) / 278))) ((f - 1) % 278) = f by
    change 1 + 278 * ((f - 1) / 278) + (f - 1) % 278 = f
    omega] at h2
  obtain ⟨h3, h4⟩ := andB_iff.1 h2
  exact ⟨h3, andB_iff.1 h4⟩

theorem gen_all : ∀ f, 0 < f → f < 7507 → genAt 191 REC CM PR f = true :=
  fun f hf0 hf => (gen_cov_fv_all f hf0 hf).1

theorem cov_all : ∀ f < 7507, covAt 7507 REC CH f = true := by
  intro f hf
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · exact (andB_iff.1 (andB_iff.1 ch10506z_ok).2).1
  · exact (gen_cov_fv_all f hf0 hf).2.1

theorem fv_all : ∀ f < 7507, fvAt FV FX REC f = true := by
  intro f hf
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · exact (andB_iff.1 (andB_iff.1 ch10506z_ok).2).2
  · exact (gen_cov_fv_all f hf0 hf).2.2

end CertificateChecks.KernelEaLat10506

end
