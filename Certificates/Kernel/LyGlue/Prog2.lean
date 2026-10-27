module

public import Certificates.Kernel.LyGlue.TabData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelLy XB
  "Certificates/Kernel/LyGlue/data/XTABS.bin" 9467 1 426015 11955874262480060165
#kc_select CertificateChecks.KernelLy XS XB.L 45

namespace CertificateChecks.KernelLy

open CFSG.KC.LyGlue CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def tl2 (t a : Nat) : Nat :=
  strictN a fun a => strictN (Nat.div a 4455) fun q => strictN (Nat.mod a 4455) fun r =>
    nIf(Nat.blt t 3, nIf(Nat.blt t 1, a, nIf(Nat.blt t 2, pg 17 (mask 17) (CS q) r,
        pg 17 (mask 17) (DS q) r)),
      nIf(Nat.blt t 6,
        strictN (Nat.add (Nat.mul 15 (Nat.sub t 3)) q) fun k => pg 17 (mask 17) (XS k) r,
        strictN (Nat.add (Nat.mul 15 (Nat.sub t 6)) q) fun k => pg 17 (mask 17) (TS k) r))

@[expose] def prog2 : List (Nat × Nat × List Nat) :=
  [(3, 0, [2, 1, 2]),
   (4, 0, [2, 1, 3]),
   (5, 0, [2, 3, 3, 2]),
   (6, 0, [2, 4, 4, 4, 4, 3]),
   (7, 0, [4, 1, 5, 1, 3, 4, 2, 1, 4, 1, 5]),
   (8, 0, [2, 1, 4, 4, 1, 4, 4, 1, 4, 3, 4]),
   (9, 0, [1, 6, 7, 6, 1, 7, 8, 1, 8, 6]),
   (10, 0, [7, 6, 7, 6, 7, 6, 7, 6, 7, 6]),
   (11, 0, [2, 2, 2, 3, 2, 5, 5, 2, 3, 2, 5, 2, 2]),
   (12, 0, [2, 4, 3, 4, 4, 3, 2]),
   (13, 0, [9, 9]),
   (14, 0, [11, 13, 12]),
   (15, 0, [10, 10]),
   (16, 0, [14, 14]),
   (17, 0, [4, 4, 3, 3, 4, 4, 3, 1]),
   (18, 0, [7]),
   (19, 0, [7, 1]),
   (20, 0, [1, 19]),
   (21, 0, [4, 1, 4, 4, 4, 2, 1, 5, 1, 5]),
   (22, 0, [3, 1, 21])]

theorem prog2_length : prog2.length = 20 := by decide +kernel

@[expose] noncomputable def stepK (s : Nat) : Bool := stepPt 66825 tl2 (prog2.getD s (0, 0, []))

theorem strictN_app (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem tl2_lo {k : Nat} (hk : k < 3) (a : Nat) : tl2 k a = tl k a := by
  unfold tl2
  simp only [strictN_app]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> rfl

theorem tl2_hi {t : Nat} (ht : 3 ≤ t) (a : Nat) : tl2 (t + 3) a = tl t a := by
  have h1 : Nat.blt (t + 3) 3 = false := Bool.eq_false_iff.2 fun h => by
    rw [Nat.blt_eq] at h
    omega
  have h2 : Nat.blt (t + 3) 6 = false := Bool.eq_false_iff.2 fun h => by
    rw [Nat.blt_eq] at h
    omega
  have b0 : Nat.beq t 0 = false := Bool.eq_false_iff.2 fun h => by
    rw [Nat.beq_eq] at h
    omega
  have b1 : Nat.beq t 1 = false := Bool.eq_false_iff.2 fun h => by
    rw [Nat.beq_eq] at h
    omega
  have b2 : Nat.beq t 2 = false := Bool.eq_false_iff.2 fun h => by
    rw [Nat.beq_eq] at h
    omega
  have e : Nat.sub (t + 3) 6 = Nat.sub t 3 := by
    change t + 3 - 6 = t - 3
    omega
  unfold tl2 tl
  simp only [strictN_app]
  rw [h1, h2, b0, b1, b2, e]

end CertificateChecks.KernelLy

end
