module

public import Certificates.Kernel.MaxD2.McLR.Enum
public import Certificates.Kernel.MaxD2.McLR.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.McLFiveLocalR
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis

theorem k_sz : szOK 275 9 = true := by quickRfl
theorem k_gp : allN 3 (fun k => permOK 275 9 (mask 9) (275 * 9) (GP k) (GPI k)) = true := by
  quickRfl
theorem k_nh : penumHdK (pidn 275 9) NE.cnt mclFiveDataR.nOrder NE.T NE.PL = true := by quickRfl
theorem k_ng : allN 5 (fun j => bAnd(wordEqK 275 9 (mask 9) (pidn 275 9) GP GPI 3
    (mclFiveDataR.nW[j]!) (NE.G j), canonK 275 9 (mask 9) (275 * 9) (NE.G j))) = true := by
  quickRfl
theorem k_ngi : allN 5 (fun j => permOK 275 9 (mask 9) (275 * 9) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_r0 : Nat.beq (REP 0) (pidn 275 9) = true := by quickRfl
theorem k_rw : allN 68 (fun i => wordEqK 275 9 (mask 9) (pidn 275 9) GP GPI 3
    (mclFiveDataR.repW[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 69 (fun i => permOK 275 9 (mask 9) (275 * 9) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 2 (fun t => bAnd(Nat.beq (mclFiveDataR.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 275)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 9 2 18 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_cnt : allN 68 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_ti : allN 68 (fun i => bIf(Nat.beq (Nat.mod (r32 CN (Nat.succ i)) 5) 0, false, true)) =
    true := by quickRfl

end CertificateChecks.KernelMaxD2.McLR

end
