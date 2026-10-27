module

public import Certificates.Kernel.TwoE6.Transport
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerLeviInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.F4M CFSG.KLie.CT CFSG.Fischer CFSG.EvenSmallLie.TwoE6.Stroth23Inner Matrix
  CFSG.Monster.B.Classical.UnitarySix CFSG.LieType.Universal.Unitary

@[expose] noncomputable def PY : Nat := nat_lit 4437956289500173845504

theorem Ymat_eq : Ymat = decM PY := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

theorem kY_det : Nat.beq (det PY) 1 = true := by quickRfl
theorem kY_iso : unitaryOK PY = true := by quickRfl
theorem kY_comm :
    Nat.beq (mmul PY (Nat.xor ONE E23)) (mmul (Nat.xor ONE E23) PY) = true := by quickRfl
theorem kY_tr :
    notB (Nat.beq (tr (mmul (mmul PY PY) PY)) (sqC (tr (mmul (mmul PY PY) PY)))) = true := by
  quickRfl

theorem cert3183 : (Ymat.det = 1)
    ∧ ((Ymat.map bar)ᵀ * antidiag 6 * Ymat = antidiag 6)
    ∧ (Ymat * (1 + Matrix.single 2 3 1) = (1 + Matrix.single 2 3 1) * Ymat)
    ∧ ((Ymat * Ymat * Ymat).trace ≠ bar (Ymat * Ymat * Ymat).trace) := by
  rw [Ymat_eq, ← decM_ONE, ← decM_E23, ← decM_xor]
  refine ⟨det_of kY_det, unitary_of kY_iso, by rw [mul_of kY_comm, decM_mmul], ?_⟩
  rw [← decM_mmul PY PY, ← decM_mmul (mmul PY PY) PY]
  exact trace_ne_of kY_tr

end CertificateChecks.KernelTwoE6

end
