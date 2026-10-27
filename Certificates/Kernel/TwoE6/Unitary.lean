module

public import Certificates.Kernel.TwoE6.UnitaryChecks
public import CFSG.Certificates.Kernel.S23UnitarySound

public section

namespace CertificateChecks.KernelTwoE6

open CFSG.KC.S23U CFSG.KC.F4M CFSG.KLie.CT CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.TwoA.Unitary

theorem cycInv_eq : cycInv = decM CV := by
  refine congrArg Matrix.of (funext fun i => ?_)
  fin_cases i <;> rfl

open Certificates in
open CFSG.EvenSmallLie.TwoE6 CFSG.Monster.B.TwoA.Unitary CFSG.Fischer in
theorem cert3177 : (rowsGeom (wordRows nuWord) 11 = zeroRows)
    ∧ (nuPowM 0 = 1)
    ∧ (nuPowM 1 = nuMat)
    ∧ (∀ i < 5, nuPowM (i + 1) = nuPowM i * nuPowM 1)
    ∧ (nuPowM 5 * nuPowM 5 * nuPowM 1 = 1)
    ∧ (Matrix.trace (nuPowM 1) ≠ Matrix.trace (barM (nuPowM 1)))
    ∧ (cycInv * cycMat = 1)
    ∧ (∀ c : Fin 6 → F4,
       IsScalarM ((∑ i : Fin 6, c i • nuPowM i) * ∑ i : Fin 6, c i • nuPowM i) →
         IsScalarM (∑ i : Fin 6, c i • nuPowM i)) :=
  sound u20Gens b6MatArr nuPowArr nuWord cycInv G20 B6 NP CV kG20 kBind3177 cycInv_eq (by
    rw [kGeom, kPows, kCyc, kScal]
    rfl)

end CertificateChecks.KernelTwoE6

end
