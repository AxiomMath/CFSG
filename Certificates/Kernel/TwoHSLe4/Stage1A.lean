module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGData

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem a_len : pgP0Code.length = 128 := by decide +kernel

theorem a_nodup : pgP0Code.Nodup := by decide +kernel

theorem a_so : ∀ a ∈ pgP0Code, fmOk a ∧ IsSO5 (toM a) := by decide +kernel

theorem a_one : fmOne ∈ pgP0Code := by decide +kernel

theorem a_reps : ∀ i : Fin 4, fmOk (pgRepsC i) ∧ IsSO5 (toM (pgRepsC i)) ∧
    fmMul (pgRepsC i) (pgRepsC i) = fmOne := by
  decide +kernel

theorem a_cj : ∀ e ∈ pgConjCode, fmOk e.2.1 ∧ IsSO5 (toM e.2.1) := by decide +kernel

theorem a_x15 : fmOk pgX15C ∧ IsSO5 (toM pgX15C) ∧ fmMul pgX15C pgTau2C = fmMul pgTau2C pgX15C ∧
    fmPow pgX15C 15 = fmOne ∧ fmPow pgX15C 3 ≠ fmOne ∧ fmPow pgX15C 5 ≠ fmOne := by
  decide +kernel

theorem a_x13 : fmOk pgX13C ∧ IsSO5 (toM pgX13C) ∧ fmMul pgX13C pgTau4C = fmMul pgTau4C pgX13C ∧
    fmPow pgX13C 13 = fmOne ∧ pgX13C ≠ fmOne := by
  decide +kernel

theorem a_f2 : ∀ k ∈ ([1, 3] : List ℕ), ∀ j ∈ ([0, 1] : List ℕ),
    fmOk (pgF2C k j) ∧ IsSO5 (toM (pgF2C k j)) ∧ fmMul (pgF2C k j) pgTau1C =
      fmMul (fmMul (pgReflC k) (if j = 0 then pgS1C else fmMul pgTau1C pgS1C)) (pgF2C k j) := by
  decide +kernel

end CertificateChecks.KernelTwoHSLe4.SO5

end
