
module

public import Certificates.Kernel.Sporadic.RawGenSl
public import Certificates.Kernel.SporSch.Ru.Lines
public import CFSG.Sporadic.Schreier.RuCheckSylowInputs
meta import CFSG.Sporadic.Schreier.RuCheckSylowInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuR

meta def strongR : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField1920 4

meta def baseR : Array Nat := CFSG.Sporadic.RuSchreier.ruBaseArr 1920 CFSG.Sporadic.RuSchreier.ruRBase

meta def strongS : Array (Array Nat) := CFSG.Sporadic.RuSchreier.ruField1920 1

meta def baseS : Array Nat := CFSG.Sporadic.RuSchreier.ruBaseArr 1920 CFSG.Sporadic.RuSchreier.ruSBase

end CertificateChecks.KernelSporSch.RuR

#ks_rawchain_sl CertificateChecks.KernelSporSch.RuRS 1920 11 0 16 0
  CertificateChecks.KernelSporSch.RuR.strongR CertificateChecks.KernelSporSch.RuR.baseR 5
  CFSG.Sporadic.RuSchreier.ruRDerivations

#ks_rawchain_sl CertificateChecks.KernelSporSch.RuSS1920 1920 11 0 16 0
  CertificateChecks.KernelSporSch.RuR.strongS CertificateChecks.KernelSporSch.RuR.baseS 4
  CFSG.Sporadic.RuSchreier.ruSDerivations

namespace CertificateChecks.KernelSporSch.RuR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem sOKR : allN 7 (fun j => Nat.beq (RuRS.S j) (RuT1920.L (Nat.add 34 j))) = true := by
  quickRfl

theorem sOKS : allN 7 (fun j => Nat.beq (RuSS1920.S j) (RuT1920.L (Nat.add 7 j))) = true := by
  quickRfl

theorem baseOKR : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruRBase)[t]!
    (pg 11 (mask 11) RuRS.BP t)) = true := by quickRfl

theorem baseOKS : allN 2 (fun t => Nat.beq (ruBaseArr 1920 ruSBase)[t]!
    (pg 11 (mask 11) RuSS1920.BP t)) = true := by quickRfl

theorem permR : allN 7 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuRS.S j) (RuRS.SI j)) =
    true := by quickRfl

theorem permS : allN 7 (fun j => permOK 1920 11 (mask 11) (1920 * 11) (RuSS1920.S j)
    (RuSS1920.SI j)) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuR

end
