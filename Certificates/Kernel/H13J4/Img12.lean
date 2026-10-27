module

public import Certificates.Kernel.H13J4.Img12Checks
public import CFSG.Certificates.Kernel.J4.ModelsSound
public import CFSG.Sporadic.HS.SmallF2Spec
public import Certificates.Data.CFSGNative.H13.J4Data

public section

namespace CertificateChecks.KernelH13.Img12

open CFSG.KJ4 CFSG.KJ4.S CFSG.KJ4.Mat CFSG.KJ4.Models

theorem letMat_LET_zero : letMat LET 0 = UP := by decide +kernel

theorem letMat_LET_two : letMat LET 2 = VP := by decide +kernel

theorem le_card_closure (U V : Matrix.GeneralLinearGroup (Fin 12) (ZMod 2))
    (hU : (U : Mat12) = toMat UP) (hV : (V : Mat12) = toMat VP) :
    2661120 ≤ Nat.card (Subgroup.closure ({U, V} : Set (Matrix.GeneralLinearGroup (Fin 12) (ZMod 2)))) := by
  rw [← chain]
  refine CFSG.Certificates.J4Chain.chainRun_le pm _
    ⟨fun l hl hg => ?_, fun _ _ _ hg => ?_, fun hg => ?_, fun hg => ?_⟩
  · interval_cases l
    · exact ⟨U, by simp, by rw [hU, letMat_LET_zero]; rfl⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact ⟨V, by simp, by rw [hV, letMat_LET_two]; rfl⟩
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
    · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim
  · exact (gm_false (by decide +kernel) hg).elim

theorem toMat_eq_rowsMatrix {P : ℕ} {R : Array ℕ}
    (h : ∀ i j : Fin 12, P.testBit (12 * i + j) = (R[i.val]?.getD 0).testBit j) :
    toMat P = CFSG.Sporadic.SmallF2.rowsMatrix 12 R := by
  ext i j
  rw [toMat_apply, CFSG.Sporadic.SmallF2.rowsMatrix_apply, CFSG.Sporadic.SmallF2.toVecD_apply, h]
  cases (R[i.val]?.getD 0).testBit j <;> rfl

theorem toMat_UP : toMat UP = CFSG.Sporadic.SmallF2.rowsMatrix 12 CFSG.Quasithin.H13.J4.Native.uRows12 :=
  toMat_eq_rowsMatrix (by decide +kernel)

theorem toMat_VP : toMat VP = CFSG.Sporadic.SmallF2.rowsMatrix 12 CFSG.Quasithin.H13.J4.Native.vRows12 :=
  toMat_eq_rowsMatrix (by decide +kernel)

theorem mul12_UP : mul12 UP UP = ident12 := by decide +kernel

theorem mul12_VP : mul12 VP (mul12 VP VP) = ident12 := by decide +kernel

theorem mul12_VP_sq_ne : (mul12 VP VP == ident12) = false := by decide +kernel

open CFSG.Sporadic.SmallF2 (rowsMatrix) in
open CFSG.Quasithin.H13.J4.Native (uRows12 vRows12) in
theorem uv_facts :
    rowsMatrix 12 uRows12 * rowsMatrix 12 uRows12 = 1 ∧
      rowsMatrix 12 vRows12 * (rowsMatrix 12 vRows12 * rowsMatrix 12 vRows12) = 1 ∧
      ∀ U V : Matrix.GeneralLinearGroup (Fin 12) (ZMod 2), (U : Mat12) = rowsMatrix 12 uRows12 →
        (V : Mat12) = rowsMatrix 12 vRows12 →
        2661120 ≤ Nat.card (Subgroup.closure
          ({U, V} : Set (Matrix.GeneralLinearGroup (Fin 12) (ZMod 2)))) := by
  refine ⟨?_, ?_, fun U V hU hV => le_card_closure U V (hU.trans toMat_UP.symm)
    (hV.trans toMat_VP.symm)⟩
  · rw [← toMat_UP, ← toMat_mul12, mul12_UP, toMat_ident12]
  · rw [← toMat_VP, ← toMat_mul12, ← toMat_mul12, mul12_VP, toMat_ident12]

end CertificateChecks.KernelH13.Img12

end
