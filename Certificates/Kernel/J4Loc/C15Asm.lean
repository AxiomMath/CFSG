module

public import Certificates.Kernel.J4Loc.C15Chk
public import Certificates.Kernel.J4Loc.TrioAsm
public import CFSG.Certificates.Kernel.J4Loc.C15Sound

public section

namespace CertificateChecks.KernelJ4Loc

open CFSG.KC.J4Q CFSG.KC.J4Loc CFSG.KD.J4Loc CFSG.KS.J4Loc CFSG.Sporadic.J4.QT
  CFSG.Quasithin.J4Loc

theorem k4179_wa : ([0, 1, 5, 3, 2, 2, 4] : List ℕ).map (fun l => letters.getD l 0) = wordZA := by
  decide

theorem k4179_wb :
    ([4, 0, 4, 3, 1, 0, 1, 5] : List ℕ).map (fun l => letters.getD l 0) = wordZB := by
  decide

theorem k4179_all :
    TrioZ.ncard = 15 ∧
      (∀ W ∈ TrioZ, wordImgF wordZA (wordImgF wordZB W) = wordImgF wordZB (wordImgF wordZA W) ∧
        wordImgF wordZA (wordImgF wordZA (wordImgF wordZA W)) = W ∧
        wordImgF wordZB (wordImgF wordZB (wordImgF wordZB W)) = W) ∧
      ∃ W ∈ TrioZ, wordImgF wordZA W ≠ W ∧ wordImgF wordZB W ≠ W ∧
        wordImgF wordZB W ≠ wordImgF wordZA W ∧
        wordImgF wordZB W ≠ wordImgF wordZA (wordImgF wordZA W) := by
  have h := c15K_sound k4174_octAll k4174_letterRows k4174_I0 k4174_V0 (by decide) (by decide) ch4179
  rw [k4179_wa, k4179_wb] at h
  exact h

theorem k4179_ncard : TrioZ.ncard = 15 := k4179_all.1

theorem k4179_rel {W : Finset ℕ} (hW : W ∈ TrioZ) :
    wordImgF wordZA (wordImgF wordZB W) = wordImgF wordZB (wordImgF wordZA W) ∧
      wordImgF wordZA (wordImgF wordZA (wordImgF wordZA W)) = W ∧
      wordImgF wordZB (wordImgF wordZB (wordImgF wordZB W)) = W :=
  k4179_all.2.1 W hW

theorem k4179_ne : ∃ W ∈ TrioZ, wordImgF wordZA W ≠ W ∧ wordImgF wordZB W ≠ W ∧
    wordImgF wordZB W ≠ wordImgF wordZA W ∧
    wordImgF wordZB W ≠ wordImgF wordZA (wordImgF wordZA W) :=
  k4179_all.2.2

end CertificateChecks.KernelJ4Loc

end
