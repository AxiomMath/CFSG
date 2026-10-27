module

public import Certificates.Kernel.MaxD2.HSP.Enum
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.HSOverData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.HSP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.HSOver

theorem k_sz : szOK 100 7 = true := by quickRfl
theorem k_gp : allN 2 (fun k => permOK 100 7 (mask 7) (100 * 7) (GP k) (GPI k)) = true := by quickRfl
theorem k_nh : penumHdK (pidn 100 7) NE.cnt hsOverDataP.nOrder NE.T NE.PL = true := by quickRfl
theorem k_ng : allN 4 (fun j => bAnd(wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2
    (hsOverDataP.nW[j]!) (NE.G j), canonK 100 7 (mask 7) (100 * 7) (NE.G j))) = true := by
  quickRfl
theorem k_ngi : allN 4 (fun j => permOK 100 7 (mask 7) (100 * 7) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_r0 : Nat.beq (REP 0) (pidn 100 7) = true := by quickRfl
theorem k_rw : allN 19 (fun i => wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2
    (hsOverDataP.repW[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 20 (fun i => permOK 100 7 (mask 7) (100 * 7) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 3 (fun t => bAnd(Nat.beq (hsOverDataP.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 100)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 7 3 21 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_cnt : allN 19 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 20).foldl (fun s i => s + hsOverDataP.nOrder *
    hsOverDataP.nOrder / (if i = 0 then NE.cnt else r32 CN i)) 0) hsOverDataP.gOrder = true := by
  quickRfl
theorem k_c16a : Nat.beq (r32 CN 1) 16 = true := by quickRfl
theorem k_c16b : Nat.beq (r32 CN 2) 16 = true := by quickRfl
theorem k_lab : labK 100 7 NE.k NE.G (fun _ => 0) = true := by quickRfl
theorem k_gen : allN 17 (fun i => bAnd(Nat.beq (hsOverDataP.genW[i]!).length 2,
    allN 2 (fun j => wordEqK 100 7 (mask 7) (pidn 100 7)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, REP (Nat.succ (Nat.add i 2))))
      (fun l => nIf(Nat.blt l NE.k, NGI l, REPI (Nat.succ (Nat.add i 2)))) 5
      ((hsOverDataP.genW[i]!)[j]!) (GP j)))) = true := by quickRfl
theorem k_pl : Nat.beq hsOverPairW.length 2 = true := by quickRfl
theorem k_pw : allN 2 (fun j => wordEqK 100 7 (mask 7) (pidn 100 7)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, nIf(Nat.beq l NE.k, REP (nat_lit 1), REP (nat_lit 2))))
      (fun l => nIf(Nat.blt l NE.k, NGI l, nIf(Nat.beq l NE.k, REPI (nat_lit 1), REPI (nat_lit 2))))
      6 (hsOverPairW[j]!) (GP j)) = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSP

end
