
module

public import Certificates.Kernel.J2Cover.AutChains
public import Certificates.Kernel.J2Cover.OddData
public import CFSG.Certificates.Kernel.J2OddSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J2CoverSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.J2Cover CFSG.KC.J2Odd
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Th.Native

theorem kOddC2B : oddK 315 9 15 (prodList 315 9 2 C2B.LR C2B.TR fun _ => true) OWC2B = true := by
  quickRfl

theorem kOddC2A : oddK 315 9 15 (prodList 315 9 3 C2A.LR C2A.TR fun _ => true) OWC2A = true := by
  quickRfl

theorem kOddCOU : oddK 315 9 21 (prodList 315 9 2 COU.LR COU.TR fun _ => true) OWCOU = true := by
  quickRfl

theorem oddC2B : oddWitnessOK 315 15
    (filterProducts 315 allTrue (chainTables 315 cent2BStrong cent2BBase) (idT 315) []) = true := by
  obtain ⟨e, c⟩ := prodList_sound (f := allTrue) (fk := fun _ => true) c2B_binds c2B_perm C2B.hl fun _ _ => rfl
  rw [e]
  exact oddK_sound (by decide) c kOddC2B

theorem oddC2A : oddWitnessOK 315 15
    (filterProducts 315 allTrue (chainTables 315 cent2AStrong cent2ABase) (idT 315) []) = true := by
  obtain ⟨e, c⟩ := prodList_sound (f := allTrue) (fk := fun _ => true) c2A_binds c2A_perm C2A.hl fun _ _ => rfl
  rw [e]
  exact oddK_sound (by decide) c kOddC2A

theorem oddCOU : oddWitnessOK 315 21
    (filterProducts 315 allTrue (chainTables 315 centOuterStrong centOuterBase) (idT 315) []) =
      true := by
  obtain ⟨e, c⟩ := prodList_sound (f := allTrue) (fk := fun _ => true) cOu_binds cOu_perm COU.hl fun _ _ => rfl
  rw [e]
  exact oddK_sound (by decide) c kOddCOU

end CertificateChecks.KernelJ2Cover

end
