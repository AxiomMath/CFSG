module

public import Certificates.Kernel.GMS78.WNEChk
public import CFSG.Certificates.Kernel.GMS78RuNESound

public section

namespace CertificateChecks.KernelGMS78.NE

open CFSG.KC.GMS CFSG.ComponentClassification.GMS78.RuNE

theorem neActPerm_eq : neActPerm = Gen.neActPermG neConjTab neConjLetters := rfl

theorem neActCheck_eq : neActCheck =
    Gen.neActCheckG neConjTab neConjLetters neMulTab neActWords neOrbitWords neOrbitWit := by
  rw [neActCheck, Gen.neActCheckG, neActPerm_eq]

theorem neW0Check_eq : neW0Check = Gen.neW0CheckG neConjTab neConjLetters [5, 0, 2, 6] := by
  rw [neW0Check, Gen.neW0CheckG, neActPerm_eq]

theorem neActCheck_true : neActCheck = true := by
  rw [neActCheck_eq]
  exact (ne_sound _ _ _ _ _ _ _ kact_ok kw0_ok).1

theorem neW0Check_true : neW0Check = true := by
  rw [neW0Check_eq]
  exact (ne_sound _ _ _ _ _ _ _ kact_ok kw0_ok).2

end CertificateChecks.KernelGMS78.NE

end
