module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxPGCore

public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
set_option synthInstance.maxSize 4096

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem c_s0 : pgS0Code.length = 120 ∧ pgS0Code.Nodup ∧ pgD0Code.length = 8 ∧ pgD0Code.Nodup := by
  decide +kernel

theorem c_ok : (∀ a ∈ pgS0Code, fmOk a) ∧ (∀ a ∈ pgD0Code, fmOk a) ∧
    fmOk pgR0C ∧ fmOk pgSf0C ∧ fmOk pgTau1C ∧ fmOk pgS1C := by
  decide +kernel

theorem c_so : (∀ a ∈ pgS0Code, IsSO5 (toM a)) ∧ ∀ a ∈ pgD0Code, IsSO5 (toM a) := by
  decide +kernel

theorem c_d0 : pgS1C ∈ pgS0Code ∧ fmMul pgS1C pgS1C = fmOne ∧
    (∀ x ∈ pgD0Code, fmMul x x = pgTau1C → x = pgR0C ∨ x = fmPow pgR0C 3) ∧
    (∀ x ∈ pgD0Code, fmMul x x = fmOne → x ≠ fmOne → x ≠ pgTau1C →
      x = pgReflC 0 ∨ x = pgReflC 1 ∨ x = pgReflC 2 ∨ x = pgReflC 3) ∧
    (∀ x ∈ pgD0Code, fmMul x x = fmOne → x ≠ fmOne → x ≠ pgTau1C → fmTr x ≠ fmTr pgTau1C) ∧
    pgR0C ∈ pgD0Code ∧ pgSf0C ∈ pgD0Code ∧ pgTau1C ∈ pgD0Code ∧
    fmMul pgR0C pgR0C = pgTau1C ∧ fmMul pgSf0C pgSf0C = fmOne ∧ fmMul pgSf0C pgR0C = pgReflC 1 ∧
    (∀ k ∈ ([0, 1, 2, 3] : List ℕ), fmMul (pgReflC k) (pgReflC k) = fmOne) ∧
    fmMul pgTau1C pgTau1C = fmOne ∧ fmMul pgTau1C pgS1C = fmMul pgS1C pgTau1C := by
  decide +kernel

end CertificateChecks.KernelTwoHSLe4.SO5

end
