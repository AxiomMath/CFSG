module

public import Certificates.Kernel.TitsOver.Three.Enum
public import Certificates.Kernel.TitsOver.Three.Sides
public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.TitsOver.Check
public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.KS.TitsOver CertificateChecks.KernelSpor.Tits2264 CFSG.StandardType.TitsThree

theorem k_pg : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (pWords[j]!) (PE.G j), canonK 1755 11 (mask 11) (1755 * 11) (PE.G j))) = true := by quickRfl
theorem k_ph : penumHdK (pidn 1755 11) PE.cnt 27 PE.T PE.PL = true := by quickRfl
theorem k_psl : penumSlK 1755 11 (mask 11) (1755 * 11) false PE.G PE.GI PE.k PE.cnt PE.T PE.PL
    PE.POS PE.SRT PE.SRI 0 27 = true := by quickRfl
theorem k_pgi : allN 2 (fun l => permOK 1755 11 (mask 11) (1755 * 11) (PE.G l) (PGI l)) = true := by
  quickRfl
theorem k_ng : allN 4 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (nWords[j]!) (NE.G j), canonK 1755 11 (mask 11) (1755 * 11) (NE.G j))) = true := by quickRfl
theorem k_nh : penumHdK (pidn 1755 11) NE.cnt 216 NE.T NE.PL = true := by quickRfl
theorem k_ngi : allN 4 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_norm : allN 4 (fun j => allN 2 (fun i =>
    bAnd(conjInK 1755 11 PE.cnt PE.T (NE.G j) (NGI j) (PE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 1755 11 PE.cnt PE.T (NGI j) (NE.G j) (PE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_sg0 : allN 6 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((lWords 0)[j]!) (S0E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S0E.G j))) = true := by
  quickRfl
theorem k_sg1 : allN 6 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((lWords 1)[j]!) (S1E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S1E.G j))) = true := by
  quickRfl
theorem k_sg2 : allN 10 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((mWords 0)[j]!) (S2E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S2E.G j))) = true := by
  quickRfl
theorem k_sg3 : allN 10 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    ((mWords 1)[j]!) (S3E.G j), canonK 1755 11 (mask 11) (1755 * 11) (S3E.G j))) = true := by
  quickRfl
theorem k_sh0 : penumHdK (pidn 1755 11) S0E.cnt 5616 S0E.T S0E.PL = true := by quickRfl
theorem k_sh1 : penumHdK (pidn 1755 11) S1E.cnt 5616 S1E.T S1E.PL = true := by quickRfl
theorem k_sh2 : penumHdK (pidn 1755 11) S2E.cnt 11232 S2E.T S2E.PL = true := by quickRfl
theorem k_sh3 : penumHdK (pidn 1755 11) S3E.cnt 11232 S3E.T S3E.PL = true := by quickRfl
theorem k_sgi0 : allN 6 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (S0E.G j) (SGI0 j)) = true := by
  quickRfl
theorem k_sgi1 : allN 6 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (S1E.G j) (SGI1 j)) = true := by
  quickRfl

theorem k_r0 : Nat.beq (REP 0) (pidn 1755 11) = true := by quickRfl
theorem k_rw : allN 456 (fun i => wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (repWords[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 457 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 2 (fun t => bAnd(Nat.beq (pairData.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 1755)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 11 2 22 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_cnt : allN 456 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 457).foldl (fun s i => s + 216 * 216 /
    (if i = 0 then NE.cnt else r32 CN i)) 0) 17971200 = true := by quickRfl
theorem k_lab : labK 1755 11 NE.k NE.G (r32 L) = true := by quickRfl
theorem k_mk : allN 457 (fun i => Nat.beq (rg 4096 (mask 4096) MK 0 i)
    (mkeyK 1755 11 28 11 (r32 MISC 0) (r32 L) (REP i))) = true := by quickRfl
theorem k_mkd : allN 457 (fun i => allN 457 (fun j => bIf(Nat.blt i j,
    bIf(Nat.beq (rg 4096 (mask 4096) MK 0 i) (rg 4096 (mask 4096) MK 0 j), false, true), true))) =
    true := by quickRfl

theorem k_kind : allN 456 (fun i => Nat.blt (pairData.kind[i]!) 5) = true := by quickRfl
theorem k_sm : allN 456 (fun i => bIf(Nat.beq (pairData.kind[i]!) 0, true,
    bAnd(Nat.blt (r32 SMQ i) (SC (Nat.sub (pairData.kind[i]!) 1)),
      Nat.beq (ST (Nat.sub (pairData.kind[i]!) 1) (r32 SMQ i)) (REP (Nat.succ i))))) = true := by
  quickRfl
theorem k_mw : allN 2 (fun k => allN 4 (fun l =>
    bAnd(Nat.blt (r32 MWQ (Nat.add (Nat.mul 4 k) l)) (SC k),
      wordBK 2 6 (r32 CertificateChecks.KernelMaxD2.TitsD.PT) (genLf 11 (mask 11) Dk)
        (genLf 11 (mask 11) DIk) ((memWords.getD k []).getD l [])
        (pg 11 (mask 11) (ST k (r32 MWQ (Nat.add (Nat.mul 4 k) l))))))) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
