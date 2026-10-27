
module

public import Certificates.Data.Kernel.PermCent.L34MTwin

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34MT

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem kChars : charsOK W1.chars = true ∧ charsOK W2.chars = true ∧ charsOK W3.chars = true ∧
    charsOK W4.chars = true := by
  decide +kernel

theorem kCover : coverC (clC rep1 W1.chars) (clC rep2 W2.chars) (clC rep3 W3.chars)
    (clC rep4 W4.chars) = true := by
  decide +kernel

theorem kQP : schP QP = true := by decide +kernel

theorem kCent : ((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length % 9 = 0 := by
  decide +kernel

theorem kE0 : siftP QP e4u0 0 = true ∧ siftP QP e4v0 0 = true ∧
    (decide (e4u0 ≠ 1) && decide (e4v0 ≠ 1) && decide (e4u0 ≠ e4v0) && decide (e4u0 ^ 2 = 1) &&
      decide (e4v0 ^ 2 = 1) && decide (e4u0 * e4v0 = e4v0 * e4u0) && decide (1 * e4u0 = e4u0 * 1) &&
      decide (1 * e4v0 = e4v0 * 1)) = true := by
  decide +kernel

theorem kE1 : siftP QP e4u1 0 = true ∧ siftP QP e4v1 0 = true ∧
    (decide (e4u1 ≠ 1) && decide (e4v1 ≠ 1) && decide (e4u1 ≠ e4v1) && decide (e4u1 ^ 2 = 1) &&
      decide (e4v1 ^ 2 = 1) && decide (e4u1 * e4v1 = e4v1 * e4u1) &&
      decide (rep1 * e4u1 = e4u1 * rep1) && decide (rep1 * e4v1 = e4v1 * rep1)) = true := by
  decide +kernel

theorem kE2 : siftP QP e4u2 0 = true ∧ siftP QP e4v2 0 = true ∧
    (decide (e4u2 ≠ 1) && decide (e4v2 ≠ 1) && decide (e4u2 ≠ e4v2) && decide (e4u2 ^ 2 = 1) &&
      decide (e4v2 ^ 2 = 1) && decide (e4u2 * e4v2 = e4v2 * e4u2) &&
      decide (rep2 * e4u2 = e4u2 * rep2) && decide (rep2 * e4v2 = e4v2 * rep2)) = true := by
  decide +kernel

theorem kE3 : siftP QP e4u3 0 = true ∧ siftP QP e4v3 0 = true ∧
    (decide (e4u3 ≠ 1) && decide (e4v3 ≠ 1) && decide (e4u3 ≠ e4v3) && decide (e4u3 ^ 2 = 1) &&
      decide (e4v3 ^ 2 = 1) && decide (e4u3 * e4v3 = e4v3 * e4u3) &&
      decide (rep3 * e4u3 = e4u3 * rep3) && decide (rep3 * e4v3 = e4v3 * rep3)) = true := by
  decide +kernel

theorem k5138_neg : coverC (clC rep1 W1.chars) [] [] [] = false ∧
    ((elemsC QP).filter fun g => eq22C g (cOf rep4) (cOf rep4) g).length % 27 ≠ 0 := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.L34MT
