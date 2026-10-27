module

public import Certificates.Kernel.SporSch.Ru.SChain4060L0
public import Certificates.Kernel.SporSch.Ru.SChain4060L1
public import Certificates.Kernel.SporSch.Ru.SChain4060L2
public import Certificates.Kernel.SporSch.Ru.SChain4060L3
public import Certificates.Kernel.SporSch.Ru.Lines
public import Certificates.Kernel.Sporadic.RawGenSl
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_join CertificateChecks.KernelSporSch.RuS4

namespace CertificateChecks.KernelSporSch.RuS4M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem sOK : allN 6 (fun j => Nat.beq (RuS4.S j) (RuT4060.L (Nat.add 33 j))) = true := by
  quickRfl

theorem baseOK : allN 2 (fun t => Nat.beq (ruBaseArr 4060 ruS4060ChainBase)[t]!
    (pg 12 (mask 12) RuS4.BP t)) = true := by quickRfl

theorem perm : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuS4.S j) (RuS4.SI j)) =
    true := by quickRfl

theorem cnt0 : Nat.beq (rcnt (RuS4.LR 0)) 2048 = true := by quickRfl
theorem cnt1 : Nat.beq (rcnt (RuS4.LR 1)) 8 = true := by quickRfl

end CertificateChecks.KernelSporSch.RuS4M

end
