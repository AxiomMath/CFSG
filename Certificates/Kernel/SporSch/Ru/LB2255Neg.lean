module

public import Certificates.Kernel.SporSch.Ru.LB2255
public import CFSG.Certificates.Kernel.Lie.CT.Core
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.LChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLB.Neg

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ru2250 CFSG.KS.Ru2255
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuLB
open CFSG.KLie.CT (notB)

theorem neg_conj : notB (conjK 4060 12 (mask 12) (gT (jOf 0)) (TK 1) Z) = true := by quickRfl

theorem neg_conjR : notB (conjRK 4060 12 (mask 12) (gT (jOf 0)) A0 (AG 1)) = true := by quickRfl

theorem neg_sq : notB (pSq (pidn 4060 12) (pidn 4060 12) (pidn 4060 12)) = true := by quickRfl

theorem neg_fib : notB (fibK 12 (mask 12) (AG 11) (pidn 4060 12) (pidn 4060 12) (pidn 4060 12)) =
    true := by quickRfl

theorem neg_ord : notB (ordK (pg 12 (mask 12) A0)) = true := by quickRfl

theorem neg_ordRep : notB (bIf(ord14Exp.getD 3 false, ordK (atK 0), bIf(ordK (atK 0), false,
    true))) = true := by quickRfl

theorem neg_blk : notB (strictB (oC 0) (fun o0 => strictB (oC 1) (fun o1 => strictB (oC 2)
    (fun o2 => Nat.beq (cnt3K RuCS.TR o0 o1 o2 (nat_lit 64) (nat_lit 2) (pC 0) (nat_lit 0)
      (nat_lit 64)) (Nat.succ (cntCB 0)))))) = true := by quickRfl

end CertificateChecks.KernelSporSch.RuLB.Neg

end
