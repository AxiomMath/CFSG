
module

public import Certificates.Kernel.MonsterB.IndOrbChecks
public import CFSG.Monster.B.Fischer.InducedCodeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelMonB.ICe CFSG.Monster.B.Fischer.indCentralHex
#kmisc_hexflat CertificateChecks.KernelMonB.ICe CFSG.Monster.B.Fischer.indCentralHex 3 3510 12 1

namespace CertificateChecks.KernelMonB.IndCentral

open CFSG.KC.IndOrb CFSG.KC.U6Orb CFSG.KLie.CT CFSG.Monster.B.Fischer CertificateChecks.KernelMonB

set_option maxRecDepth 100000

theorem kX : ∀ n < 22, 22 ≤ fget (ICe.F 0) n 12 ∧ fget (ICe.F 0) n 12 < 1046 ∧
    red 12 pivK rowK (spreadW (fget (ICe.F 0) n 12 - 22) ^^^ 2 ^ n) = 0 := by
  decide +kernel

theorem kW1 : ∀ j < 22, fget (ICe.F 0) (22 + fget (IW 0) (1 + j) 12) 12 < 22 ∧
    red 12 pivK rowK (spreadW (fget (IW 0) (1 + j) 12) ^^^
      2 ^ fget (ICe.F 0) (22 + fget (IW 0) (1 + j) 12) 12) = 0 := by
  decide +kernel

theorem kW0 : mapOK (ICe.F 0) (IW 0) 12 0 1 22 (Nat.add 22) = true := by quickRfl

theorem kW3 : mapOK (ICe.F 0) (IW 0) 12 23 231 22 (Nat.add 22) = true := by quickRfl

theorem kW7 : mapOK (ICe.F 0) (IW 0) 12 254 770 22 (fun u => Nat.add 1046 (fget (IW 6) u 12)) =
    true := by quickRfl

theorem kZ0 : mapOK (ICe.F 0) (IZ 0) 12 0 462 1046 (Nat.add 1046) = true := by quickRfl

theorem kZ24 : backOK (ICe.F 0) (IZ 0) 462 770 1046 22 (IW 6) (IW 1) 1024 254 770 = true := by
  quickRfl

theorem kZ1 : mapOK (ICe.F 0) (IZ 0) 12 1232 1232 1046 (fun n => Nat.add 1046 (fget (IZ 6) n 12)) =
    true := by quickRfl

end CertificateChecks.KernelMonB.IndCentral

end
