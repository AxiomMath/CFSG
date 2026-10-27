module

public import Certificates.Kernel.TwoE6.Transport
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23LeviInputs
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth22Native
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.F4M CFSG.KLie.CT CFSG.Fischer CFSG.EvenSmallLie.TwoE6 Matrix
  CFSG.Monster.B.Classical.UnitarySix CFSG.LieType.Universal.Unitary

@[expose] noncomputable def PA : Nat := nat_lit 1180663682709764195329

@[expose] noncomputable def PN : Nat := nat_lit 3019159921310835990720

@[expose] noncomputable def PP0 : Nat := nat_lit 2166744086023916582914
@[expose] noncomputable def PP1 : Nat := nat_lit 63150962419065161130
@[expose] noncomputable def PP2 : Nat := nat_lit 3213941091635674720441

theorem outA_eq : outA = decM PA := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

theorem outN_eq : outN = decM PN := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

theorem outNPow_eq0 : outNPow 0 = decM PP0 := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

theorem outNPow_eq1 : outNPow 1 = decM PP1 := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

theorem outNPow_eq2 : outNPow 2 = decM PP2 := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

theorem kA_det : Nat.beq (det PA) 1 = true := by quickRfl
theorem kA_iso : unitaryOK PA = true := by quickRfl
theorem kN_det : Nat.beq (det PN) 1 = true := by quickRfl
theorem kN_iso : unitaryOK PN = true := by quickRfl
theorem kA_beta : Nat.beq (mmul PA (barM PA)) ONE = true := by quickRfl
theorem kN_A : Nat.beq (mmul (mmul PN PA) (barM PN)) PA = true := by quickRfl
theorem kN_sq : Nat.beq (mmul PN PN) PP0 = true := by quickRfl
theorem kP0 : Nat.beq (mmul PP0 PP0) PP1 = true := by quickRfl
theorem kP1 : Nat.beq (mmul PP1 PP1) PP2 = true := by quickRfl
theorem kP2 : Nat.beq (mmul (mmul PP2 PP0) PN) ONE = true := by quickRfl

theorem cert3141 : (outA.det = 1)
    ∧ ((outA.map bar)ᵀ * antidiag 6 * outA = antidiag 6)
    ∧ (outN.det = 1)
    ∧ ((outN.map bar)ᵀ * antidiag 6 * outN = antidiag 6)
    ∧ (outA * betaM outA = 1)
    ∧ (outN * outA * betaM outN = outA)
    ∧ (outN * outN = outNPow 0)
    ∧ (outNPow 0 * outNPow 0 = outNPow 1)
    ∧ (outNPow 1 * outNPow 1 = outNPow 2)
    ∧ (outNPow 2 * outNPow 0 * outN = 1) := by
  rw [outA_eq, outN_eq, outNPow_eq0, outNPow_eq1, outNPow_eq2, betaM_eq, betaM_eq]
  refine ⟨det_of kA_det, unitary_of kA_iso, det_of kN_det, unitary_of kN_iso, ?_, ?_,
    mul_of kN_sq, mul_of kP0, mul_of kP1, ?_⟩
  · rw [mul_of kA_beta, decM_ONE]
  · rw [← decM_mmul PN PA, mul_of kN_A]
  · rw [← decM_mmul PP2 PP0, mul_of kP2, decM_ONE]

end CertificateChecks.KernelTwoE6

end
