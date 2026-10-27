module

public import Certificates.Kernel.MaxD2.TitsD.Enum
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Kernel.TitsOver.Five.LEnum
public import Certificates.Kernel.TitsOver.Five.Data
public import Certificates.Kernel.TitsOver.Five.LData
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.TitsOver.Check
public import CFSG.LocalAnalysis.StandardType.TitsFiveOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Five

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.KS.TitsOver CertificateChecks.KernelSpor.Tits2264 CFSG.StandardType.TitsFive
open CertificateChecks.KernelMaxD2
open CertificateChecks.KernelMaxD2.TitsD (PT)

theorem k_lg : allN 4 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (lWords[j]!) (LE.G j), canonK 1755 11 (mask 11) (1755 * 11) (LE.G j))) = true := by quickRfl
theorem k_lgi : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (LE.G j) (LGI j)) = true := by
  quickRfl
theorem k_lh : penumHdK (pidn 1755 11) LE.cnt 7800 LE.T LE.PL = true := by quickRfl

theorem k_r0 : Nat.beq (REP 0) (pidn 1755 11) = true := by quickRfl
theorem k_rw : allN 24 (fun i => wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (repWords[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 25 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_cnt : allN 24 (fun i => Nat.beq (posCnt TitsD.NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 25).foldl (fun s i => s + 1200 * 1200 /
    (if i = 0 then TitsD.NE.cnt else r32 CN i)) 0) 17971200 = true := by quickRfl
theorem k_mk : allN 25 (fun i => Nat.beq (rg 512 (mask 512) MK 0 i)
    (mkeyK 1755 11 28 11 (r32 CertificateChecks.KernelMaxD2.TitsD.MISC 1)
      (r32 CertificateChecks.KernelMaxD2.TitsD.L) (REP i))) = true := by quickRfl
theorem k_mkd : allN 25 (fun i => allN 25 (fun j => bIf(Nat.blt i j,
    bIf(Nat.beq (rg 512 (mask 512) MK 0 i) (rg 512 (mask 512) MK 0 j), false, true), true))) =
    true := by quickRfl
theorem k_pgi : allN 2 (fun l => permOK 1755 11 (mask 11) (1755 * 11) (TitsD.RE.G l) (PGI l)) = true := by
  quickRfl
theorem k_gen : allN 24 (fun i => bIf(Nat.beq (pairData.kind[i]!) 0,
    bAnd(Nat.beq (genWords[i]!).length 2, allN 2 (fun j =>
      wordBK 4 6 (r32 PT) (pairLf 11 (mask 11) (TitsD.RE.G 0) (TitsD.RE.G 1) (REP (Nat.succ i)) (REPI (Nat.succ i)))
        (pairLf 11 (mask 11) (PGI 0) (PGI 1) (REP (Nat.succ i)) (REPI (Nat.succ i)))
        ((genWords[i]!)[j]!) (pg 11 (mask 11) (Dk j)))), true)) = true := by quickRfl
theorem k_sm1 : Nat.blt (r32 LSM 0) LE.cnt = true := by quickRfl
theorem k_sm2 : Nat.beq (LE.T (r32 LSM 0)) (REP 24) = true := by quickRfl
theorem k_sg : allN 4 (fun j => wordBK 4 6 (r32 PT) (pairLf 11 (mask 11) (TitsD.RE.G 0) (TitsD.RE.G 1) (REP 24)
    (REPI 24)) (pairLf 11 (mask 11) (PGI 0) (PGI 1) (REP 24) (REPI 24)) ((sideGenWords[23]!)[j]!)
    (pg 11 (mask 11) (LE.G j))) = true := by quickRfl

theorem k_lr0 : Nat.beq (LREP 0) (pidn 1755 11) = true := by quickRfl
theorem k_lrw : allN 6 (fun i => wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (lMaxData.repW[i]!) (LREP (Nat.succ i))) = true := by quickRfl
theorem k_lri : allN 7 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (LREP i) (LREPI i)) = true := by
  quickRfl
theorem k_lpts : allN 3 (fun t => bAnd(Nat.beq (lMaxData.fpPts[t]!) (r32 LPT t),
    Nat.blt (r32 LPT t) 1755)) = true := by quickRfl
theorem k_lcnt : allN 6 (fun i => Nat.beq (posCnt LE.cnt LH (Nat.succ i)) (r32 LCN (Nat.succ i))) =
    true := by quickRfl
theorem k_lsum : Nat.beq ((List.range 7).foldl (fun s i => s + 7800 * 7800 /
    (if i = 0 then LE.cnt else r32 LCN i)) 0) 17971200 = true := by quickRfl
theorem k_lmk : allN 7 (fun i => Nat.beq (rg 128 (mask 128) LMK 0 i)
    (mkeyK 1755 11 28 11 (r32 LMISC 0) (r32 LL) (LREP i))) = true := by quickRfl
theorem k_lgen : allN 6 (fun i => bAnd(Nat.beq (lMaxData.genW[i]!).length 2,
    allN 2 (fun j => wordEqK 1755 11 (mask 11) (pidn 1755 11)
      (fun l => nIf(Nat.blt l 4, LE.G l, LREP (Nat.succ i)))
      (fun l => nIf(Nat.blt l 4, LGI l, LREPI (Nat.succ i))) 5
      ((lMaxData.genW[i]!)[j]!) (Dk j)))) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Five

end
