module

public import Certificates.Kernel.Sporadic.RawGenSch
public import Certificates.Kernel.SporSch.Ru.Lines
public import Certificates.Kernel.Sporadic.RawGenSchPFJ
public import Certificates.Kernel.SporSch.Ru.LCPLv
public import Certificates.Kernel.SporSch.Ru.LCPF0
public import Certificates.Kernel.SporSch.Ru.LCPF1
public import Certificates.Kernel.SporSch.Ru.LCPF2
public import Certificates.Kernel.SporSch.Ru.LCPF3
public import CFSG.Sporadic.Schreier.RuCheckLInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain_sl2_joinpf CertificateChecks.KernelSporSch.RuLS 1

namespace CertificateChecks.KernelSporSch.RuL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.RuSchreier CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem sOK : allN 6 (fun j => Nat.beq (RuLS.S j) (RuT4060.L (Nat.add 39 j))) = true := by
  quickRfl

theorem baseOK : allN 2 (fun t => Nat.beq (ruBaseArr 4060 ruLChainBase)[t]!
    (pg 12 (mask 12) RuLS.BP t)) = true := by quickRfl

theorem perm : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuLS.S j) (RuLS.SI j)) =
    true := by quickRfl

theorem cnt0 : Nat.beq (rcnt (RuLS.LR 0)) 1820 = true := by quickRfl
theorem cnt1 : Nat.beq (rcnt (RuLS.LR 1)) 64 = true := by quickRfl

end CertificateChecks.KernelSporSch.RuL

end
