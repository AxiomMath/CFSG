
module

public import Certificates.Kernel.KDense.Y443.Base
public import CFSG.Certificates.Kernel.KDense.Y443.C10111All
public import CFSG.Certificates.Kernel.KDense.Y443.C9356All

public section

namespace CertificateChecks.KernelKDense.Y443

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDense.Y443 CFSG.Monster.AxisCount CFSG.YGroups.Y443

set_option maxRecDepth 100000

theorem pl10111 : planOK (words p10111) CFSG.KD.Y443.c10111.CH 39 CFSG.KD.Y443.c10111.IT = true := by quickRfl
theorem pl9356 : planOK (words p9356) CFSG.KD.Y443.c9356.CH 54 CFSG.KD.Y443.c9356.IT = true := by quickRfl

theorem lo10111 : pairsLetterOK p10111 = true := by quickRfl
theorem lo9356 : pairsLetterOK p9356 = true := by quickRfl

theorem k10111 : ∀ k < 39, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p10111) CFSG.KD.Y443.c10111.S
    (CFSG.KD.Y443.c10111.CH k) = true := by kd_all CFSG.KD.Y443.c10111 39
theorem k9356 : ∀ k < 54, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words p9356) CFSG.KD.Y443.c9356.S
    (CFSG.KD.Y443.c9356.CH k) = true := by kd_all CFSG.KD.Y443.c9356 54

theorem hS10111 : ∀ x < 3, CFSG.KD.Y443.c10111.S x = CFSG.KD.KDF.I x := by
  intro x hx
  interval_cases x <;> rfl

theorem hS9356 : ∀ x < 3, CFSG.KD.Y443.c9356.S x = CFSG.KD.KDF.I x := by
  intro x hx
  interval_cases x <;> rfl

theorem bray_eq (t : ℕ) (ht : t < 3) :
    wordLin (p10111.getD t ([], [])).1 = wordLin (p10111.getD t ([], [])).2 := by
  apply eq_of_three
  intro x hx
  have h := item_cong lo10111 hS10111 pl10111 k10111 (t + 3 * x) (by
    change _ < 11; omega) (by interval_cases t <;> interval_cases x <;> decide)
  have hw : CFSG.KD.Y443.c10111.IT[t + 3 * x]! % 4 = x := by
    interval_cases t <;> interval_cases x <;> decide
  have hp : p10111.getD (t + 3 * x) ([], []) = p10111.getD t ([], []) := by
    interval_cases t <;> interval_cases x <;> rfl
  rwa [hw, hp] at h

theorem c10111 :
    wordLin (omegaWord ++ kWord) = wordLin (eWord ++ omegaWord) ∧
      wordLin gWord = wordLin (xWord ++ kWord ++ xWord ++ kWord) ∧
      wordLin (xWord ++ gWord) = wordLin (gWord ++ xWord) ∧
      wordLin (tWord ++ gWord) ≠ wordLin (gWord ++ tWord) ∧
      wordLin (tWord ++ gWord) ≠ wordLin (gWord ++ tWord ++ xWord) :=
  ⟨bray_eq 0 (by decide), bray_eq 1 (by decide), bray_eq 2 (by decide),
    item_ne lo10111 hS10111 pl10111 k10111 9 (by decide) (by decide),
    item_ne lo10111 hS10111 pl10111 k10111 10 (by decide) (by decide)⟩

theorem c9356 : wordLin EdgeNoncomm.edgeWord ≠ 1 := by
  have h := item_ne lo9356 hS9356 pl9356 k9356 0 (by decide) (by decide)
  rwa [show (p9356.getD 0 ([], [])).2 = [] from rfl, wordLin_nil] at h

end CertificateChecks.KernelKDense.Y443

end
