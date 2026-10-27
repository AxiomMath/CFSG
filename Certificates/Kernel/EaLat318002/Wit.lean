module

public import Certificates.Kernel.EaLat318002.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTPermSound
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

namespace CertificateChecks.KernelEaLat318002

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.EaLat

set_option maxRecDepth 100000

@[expose] noncomputable def ch318002w (k : Nat) : Bool :=
  allN (nat_lit 16) fun d => letB (Nat.add (Nat.mul (nat_lit 16) k) d) fun i =>
    impB (Nat.blt i (nat_lit 191)) (letB (CM i) fun ci => letB (PR i) fun pi =>
      allN i fun j => impB (notB (bit ci j))
        (Nat.blt (fld pi (Nat.mul (nat_lit 8) j) (nat_lit 255)) (nat_lit 24)))

#kc_each ch318002w 0 12

theorem slices_w : ∀ k < 12, ch318002w k = true := by
  intro k hk
  interval_cases k
  exacts [ch318002w0, ch318002w1, ch318002w2, ch318002w3, ch318002w4, ch318002w5, ch318002w6,
    ch318002w7, ch318002w8, ch318002w9, ch318002w10, ch318002w11]

theorem wit_all : ∀ i < 191, ∀ j < i, bit (CM i) j = false → fld (PR i) (8 * j) 255 < 24 := by
  intro i hi j hj hb
  have h := slices_w (i / 16) (by omega)
  rw [ch318002w, allN_iff] at h
  have h2 := h (i % 16) (Nat.mod_lt _ (by norm_num))
  rw [letB_eq, show Nat.add (Nat.mul 16 (i / 16)) (i % 16) = i by
    change 16 * (i / 16) + i % 16 = i
    omega, impB_iff, letB_eq, letB_eq, allN_iff] at h2
  have h3 := h2 (blt_iff.2 hi) j hj
  rw [impB_iff, hb] at h3
  exact blt_iff.1 (h3 rfl)

end CertificateChecks.KernelEaLat318002

end
