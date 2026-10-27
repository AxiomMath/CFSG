module

public import Certificates.Kernel.SporSch.Ru.LA2254
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLA.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2254
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLA
  CertificateChecks.KernelSporSch.RuLB
open CFSG.KLie.CT (notB)

theorem neg_comm : notB (cmK 4060 12 (mask 12) (Y0 0) (pidn 4060 12) (RuW.LG 0)) = true := by
  quickRfl

theorem neg_fix : notB (Nat.beq (fixCntK 4060 (ytK 0 4)) (inv (Nat.add (Nat.mul 7 10) 1))) =
    true := by quickRfl

theorem neg_orb : notB (strictB oL0 (fun o0 => strictB oL1 (fun o1 =>
    Nat.beq (cntK RuLS.TR o0 o1 (nat_lit 64) (pOF 12) (nat_lit 0) (nat_lit 1820))
      (inv (Nat.mul 7 13))))) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuLA.Neg

end
