module

public import Certificates.Kernel.EaLat318002.Checks
public import Certificates.Kernel.EaLat318002.Prof
import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelEaLat318002

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

theorem slices_e : ∀ k < 8, ch318002e k = true := by
  intro k hk
  interval_cases k
  exacts [ch318002e0, ch318002e1, ch318002e2, ch318002e3, ch318002e4, ch318002e5, ch318002e6,
    ch318002e7]

theorem slices_u : ∀ k < 12, ch318002u k = true := by
  intro k hk
  interval_cases k
  exacts [ch318002u0, ch318002u1, ch318002u2, ch318002u3, ch318002u4, ch318002u5, ch318002u6,
    ch318002u7, ch318002u8, ch318002u9, ch318002u10, ch318002u11]

theorem slices_g : ∀ k < 27, ch318002g k = true := by
  intro k hk
  interval_cases k
  exacts [ch318002g0, ch318002g1, ch318002g2, ch318002g3, ch318002g4, ch318002g5, ch318002g6,
    ch318002g7, ch318002g8, ch318002g9, ch318002g10, ch318002g11, ch318002g12, ch318002g13,
    ch318002g14, ch318002g15, ch318002g16, ch318002g17, ch318002g18, ch318002g19, ch318002g20,
    ch318002g21, ch318002g22, ch318002g23, ch318002g24, ch318002g25, ch318002g26]

theorem slices_p : ∀ k < 27, ch318002p k = true := by
  intro k hk
  interval_cases k
  exacts [ch318002p0, ch318002p1, ch318002p2, ch318002p3, ch318002p4, ch318002p5, ch318002p6,
    ch318002p7, ch318002p8, ch318002p9, ch318002p10, ch318002p11, ch318002p12, ch318002p13,
    ch318002p14, ch318002p15, ch318002p16, ch318002p17, ch318002p18, ch318002p19, ch318002p20,
    ch318002p21, ch318002p22, ch318002p23, ch318002p24, ch318002p25, ch318002p26]

theorem list_all : ∀ e < 1024,
    CFSG.KC.Misc.Clos.treeAt (mul 24) (one 24) GR 4 EC PA e = true ∧
      CFSG.KC.Misc.Clos.sortAt 1024 EC SG e = true ∧
      CFSG.KC.Misc.Clos.closedAt (mul 24) GR 4 1024 EC CT e = true ∧ tagAt (one 24) e = true := by
  intro e he
  have h := slices_e (e / 128) (by omega)
  rw [ch318002e, letB_eq, allN_iff] at h
  have h2 := h (e % 128) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.mul 128 (e / 128)) (e % 128) = e by
    change 128 * (e / 128) + e % 128 = e
    omega] at h2
  obtain ⟨h3, h4⟩ := andB_iff.1 h2
  obtain ⟨h5, h6⟩ := andB_iff.1 h4
  obtain ⟨h7, h8⟩ := andB_iff.1 h6
  exact ⟨h3, h5, h7, h8⟩

theorem uni_all : ∀ i < 191, uniAt (mul 24) (one 24) 191 V CM PR ncw24 i = true := by
  intro i hi
  have h := slices_u (i / 16) (by omega)
  rw [ch318002u, allN_iff] at h
  have h2 := h (i % 16) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.mul 16 (i / 16)) (i % 16) = i by
    change 16 * (i / 16) + i % 16 = i
    omega, impB_iff] at h2
  exact h2 (blt_iff.2 hi)

theorem base_ok : baseOK 191 REC = true := (andB_iff.1 ch318002z_ok).1

theorem gen_cov_all : ∀ f, 0 < f → f < 7507 →
    genAt 191 REC CM PR f = true ∧ covAt 7507 REC CH f = true := by
  intro f hf0 hf
  have h := slices_g ((f - 1) / 278) (by omega)
  rw [ch318002g, allN_iff] at h
  have h2 := h ((f - 1) % 278) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.add 1 (Nat.mul 278 ((f - 1) / 278))) ((f - 1) % 278) = f by
    change 1 + 278 * ((f - 1) / 278) + (f - 1) % 278 = f
    omega] at h2
  exact andB_iff.1 h2

theorem gen_all : ∀ f, 0 < f → f < 7507 → genAt 191 REC CM PR f = true :=
  fun f hf0 hf => (gen_cov_all f hf0 hf).1

theorem cov_all : ∀ f < 7507, covAt 7507 REC CH f = true := by
  intro f hf
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · exact (andB_iff.1 ch318002z_ok).2
  · exact (gen_cov_all f hf0 hf).2

theorem prof_all : ∀ f < 7507, profW V f = true := by
  intro f hf
  rcases Nat.eq_zero_or_pos f with rfl | hf0
  · exact ch318002p_zero
  have h := slices_p ((f - 1) / 278) (by omega)
  rw [ch318002p, allN_iff] at h
  have h2 := h ((f - 1) % 278) (Nat.mod_lt _ (by norm_num))
  rwa [show Nat.add (Nat.add 1 (Nat.mul 278 ((f - 1) / 278))) ((f - 1) % 278) = f by
    change 1 + 278 * ((f - 1) / 278) + (f - 1) % 278 = f
    omega] at h2

end CertificateChecks.KernelEaLat318002

end
