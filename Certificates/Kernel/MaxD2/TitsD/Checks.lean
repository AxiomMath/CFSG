module

public import Certificates.Kernel.MaxD2.TitsD.Enum
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Kernel.Sporadic.Tits.Words2264
public import Certificates.Data.TitsFiveLocal
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CertificateChecks.KernelSpor.Tits2264 Certificates.MaxD2Perm

theorem k_rg0 : wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2 titsDData.uW (RE.G 0) = true := by
  quickRfl
theorem k_rg1 : wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2 titsDData.vW (RE.G 1) = true := by
  quickRfl
theorem k_rgc : allN 2 (fun j => canonK 1755 11 (mask 11) (1755 * 11) (RE.G j)) = true := by
  quickRfl
theorem k_rh : penumHdK (pidn 1755 11) RE.cnt (titsDData.p ^ 2) RE.T RE.PL = true := by quickRfl
theorem k_rsl : penumSlK 1755 11 (mask 11) (1755 * 11) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 25 = true := by quickRfl
theorem k_nh : penumHdK (pidn 1755 11) NE.cnt titsDData.nOrder NE.T NE.PL = true := by quickRfl
theorem k_ng : allN 5 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (titsDData.nW[j]!) (NE.G j), canonK 1755 11 (mask 11) (1755 * 11) (NE.G j))) = true := by
  quickRfl
theorem k_ngi : allN 5 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_norm : allN 5 (fun j => allN 2 (fun i =>
    bAnd(conjInK 1755 11 RE.cnt RE.T (NE.G j) (NGI j) (RE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 1755 11 RE.cnt RE.T (NGI j) (NE.G j) (RE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_mv : notInK RE.cnt RE.T (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (Dk 0) (RE.G 0))
    (DIk 0)) = true := by quickRfl
theorem k_tw : wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2 titsDData.tW (TT 0) = true := by
  quickRfl
theorem k_tp : permOK 1755 11 (mask 11) (1755 * 11) (TT 0) (TT 1) = true := by quickRfl
theorem k_th1 : Nat.blt (r32 MISC 0) NE.cnt = true := by quickRfl
theorem k_th2 : Nat.beq (NE.T (r32 MISC 0)) (TT 0) = true := by quickRfl
theorem k_tk : torusK 1755 11 titsDData.p RE.cnt titsDData.tm titsDData.tlam titsDData.te RE.T
    (TT 0) (TT 1) = true := by quickRfl
theorem k_cent : allN NE.cnt (fun k => centK 1755 11 RE.cnt NE.T RE.T (RE.G 0) (RE.G 1) (r32 CH k) k) =
    true := by quickRfl
theorem k_r0 : Nat.beq (REP 0) (pidn 1755 11) = true := by quickRfl
theorem k_rw : allN 24 (fun i => wordEqK 1755 11 (mask 11) (pidn 1755 11) Dk DIk 2
    (titsDData.repW[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 25 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 6 (fun t => bAnd(Nat.beq (titsDData.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 1755)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 11 6 66 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_cnt : allN 24 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 25).foldl (fun s i => s + titsDData.nOrder * titsDData.nOrder /
    (if i = 0 then NE.cnt else r32 CN i)) 0) titsDData.gOrder = true := by quickRfl
theorem k_lab : labK 1755 11 NE.k NE.G (r32 L) = true := by quickRfl
theorem k_mk : allN 25 (fun i => Nat.beq (rg 512 (mask 512) MK 0 i)
    (mkeyK 1755 11 28 11 (r32 MISC 1) (r32 L) (REP i))) = true := by quickRfl
theorem k_mkd : allN 25 (fun i => allN 25 (fun j => bIf(Nat.blt i j,
    bIf(Nat.beq (rg 512 (mask 512) MK 0 i) (rg 512 (mask 512) MK 0 j), false, true), true))) =
    true := by quickRfl
theorem k_gen : allN 24 (fun i => bAnd(Nat.beq (titsDData.genW[i]!).length 2,
    allN 2 (fun j => wordEqK 1755 11 (mask 11) (pidn 1755 11)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, REP (Nat.succ i)))
      (fun l => nIf(Nat.blt l NE.k, NGI l, REPI (Nat.succ i))) 6
      ((titsDData.genW[i]!)[j]!) (Dk j)))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsD

end
