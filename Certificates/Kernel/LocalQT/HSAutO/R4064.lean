module

public import Certificates.Kernel.LocalQT.HSAutO.D4064
public import Certificates.Kernel.LocalQT.SV.C4126T
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.HO

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.HSAutN CFSG.KS.HSAutO
open CFSG.KD.LQT.C4126 CFSG.QuasithinUnique.Id2519.HSAut

@[expose] noncomputable def lq (l : Nat) : Nat := HC.F (Nat.add (nat_lit 22) l)

theorem canon_ok : allN 4 (fun l => canonK 3850 12 (mask 12) (3850 * 12) (lq l)) = true := by
  quickRfl

theorem restr_ok : strictB (wfoldR lq e1Letters) (fun E1 => strictB (wfoldR lq e2Letters)
    (fun E2 => bAnd(restrK E1 (A.G 0) OP, bAnd(restrK E2 (A.G 1) OP,
      bAnd(qInvK E1 (QM 0), bAnd(qInvK E2 (QM 0),
      bAnd(bitK (QM 0) 18, (bitK (QM 0) (img (lq 1) 18)).not))))))) = true := by
  quickRfl

theorem gens_ok : allN 2 (fun j => bAnd(canonK 35 6 (mask 6) 210 (A.G j),
    bAnd(canonK 35 6 (mask 6) 210 (A.GI j), invEqK 35 6 (mask 6) 210 (A.G j) (A.GI j)))) =
    true := by
  quickRfl

theorem head_ok : bAnd(penumHdK (pidn 35 6) A.cnt 20160 A.T A.PL, bAnd(Nat.beq A.cnt 20160,
    bAnd(Nat.beq A.k 2, bAnd(repK LAB REP A.cnt, Nat.beq (r32 LAB 0) 0)))) = true := by
  quickRfl

theorem sum_ok : allN 14 (fun l => Nat.beq (sumVC VC l 315) classSizes[l]!) = true := by
  quickRfl

end CFSG.KD.LQT.HO

end
