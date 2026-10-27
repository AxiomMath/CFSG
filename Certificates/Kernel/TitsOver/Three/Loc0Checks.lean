module

public import Certificates.Kernel.TitsOver.Three.SEnum0
public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.TitsOver.Three.Loc0Data
public import Certificates.Data.Kernel.MaxD2.Check
public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.StandardType.TitsThree

theorem c0_rg : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 6
    ((Certificates.MaxD2Perm.rWs (lLocalData 0 ()))[j]!) (C0RE.G j),
    canonK 1755 11 (mask 11) (1755 * 11) (C0RE.G j))) = true := by quickRfl
theorem c0_rh : penumHdK (pidn 1755 11) C0RE.cnt 9 C0RE.T C0RE.PL = true := by quickRfl
theorem c0_rsl : penumSlK 1755 11 (mask 11) (1755 * 11) false C0RE.G C0RE.GI C0RE.k C0RE.cnt C0RE.T
    C0RE.PL C0RE.POS C0RE.SRT C0RE.SRI 0 9 = true := by quickRfl
theorem c0_nh : penumHdK (pidn 1755 11) C0NE.cnt 432 C0NE.T C0NE.PL = true := by quickRfl
theorem c0_ng : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 6
    ((lLocalData 0 ()).nW[j]!) (C0NE.G j), canonK 1755 11 (mask 11) (1755 * 11) (C0NE.G j))) =
    true := by quickRfl
theorem c0_ngi : allN 2 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (C0NE.G j) (C0NGI j)) =
    true := by quickRfl
theorem c0_norm : allN 2 (fun j => allN 2 (fun i =>
    bAnd(conjInK 1755 11 C0RE.cnt C0RE.T (C0NE.G j) (C0NGI j) (C0RE.G i)
      (r32 C0NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 1755 11 C0RE.cnt C0RE.T (C0NGI j) (C0NE.G j) (C0RE.G i)
      (r32 C0NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem c0_mv : notInK C0RE.cnt C0RE.T (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (S0E.G 2)
    (C0RE.G 0)) (SGI0 2)) = true := by quickRfl
theorem c0_tw : wordEqK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 6 (lLocalData 0 ()).tW (C0TT 0) =
    true := by quickRfl
theorem c0_tp : permOK 1755 11 (mask 11) (1755 * 11) (C0TT 0) (C0TT 1) = true := by quickRfl
theorem c0_th1 : Nat.blt (r32 C0MISC 0) C0NE.cnt = true := by quickRfl
theorem c0_th2 : Nat.beq (C0NE.T (r32 C0MISC 0)) (C0TT 0) = true := by quickRfl
theorem c0_tk : torusK 1755 11 3 C0RE.cnt 4 2 4 C0RE.T (C0TT 0) (C0TT 1) = true := by quickRfl
theorem c0_cent : allN C0NE.cnt (fun k => centK 1755 11 C0RE.cnt C0NE.T C0RE.T (C0RE.G 0) (C0RE.G 1)
    (r32 C0CH k) k) = true := by quickRfl
theorem c0_r0 : Nat.beq (C0REP 0) (pidn 1755 11) = true := by quickRfl
theorem c0_rw : wordEqK 1755 11 (mask 11) (pidn 1755 11) S0E.G SGI0 6 ((lLocalData 0 ()).repW[0]!)
    (C0REP 1) = true := by quickRfl
theorem c0_ri : allN 2 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (C0REP i) (C0REPI i)) = true := by
  quickRfl
theorem c0_pts1 : Nat.beq ((lLocalData 0 ()).fpPts[0]!) (r32 C0PT 0) = true := by quickRfl
theorem c0_pts2 : Nat.blt (r32 C0PT 0) 1755 = true := by quickRfl
theorem c0_srt : allN C0NE.cnt (sortK 11 1 11 C0NE.cnt (r32 C0PT) C0NE.T C0FS C0KS) = true := by
  quickRfl
theorem c0_test : repK 1755 11 1 11 C0NE.cnt (r32 C0PT) C0NE.T C0FS C0KS C0REP C0REPI C0RB C0H 1 =
    true := by quickRfl
theorem c0_cnt : Nat.beq (posCnt C0NE.cnt C0H 1) (r32 C0CN 1) = true := by quickRfl
theorem c0_sum : Nat.beq ((List.range 2).foldl (fun s i => s + 432 * 432 /
    (if i = 0 then C0NE.cnt else r32 C0CN i)) 0) 5616 = true := by quickRfl
theorem c0_lab : labK 1755 11 C0NE.k C0NE.G (r32 C0L) = true := by quickRfl
theorem c0_mk : allN 2 (fun i => Nat.beq (rg 1024 (mask 1024) C0MK 0 i)
    (mkeyK 1755 11 28 11 (r32 C0MISC 1) (r32 C0L) (C0REP i))) = true := by quickRfl
theorem c0_mkd : (Nat.beq (rg 1024 (mask 1024) C0MK 0 0) (rg 1024 (mask 1024) C0MK 0 1)).not =
    true := by quickRfl
theorem c0_gen1 : Nat.beq ((lLocalData 0 ()).genW[0]!).length 6 = true := by quickRfl
theorem c0_gen2 : allN 6 (fun j => wordEqK 1755 11 (mask 11) (pidn 1755 11)
    (fun l => nIf(Nat.blt l C0NE.k, C0NE.G l, C0REP 1))
    (fun l => nIf(Nat.blt l C0NE.k, C0NGI l, C0REPI 1)) 3
    (((lLocalData 0 ()).genW[0]!)[j]!) (S0E.G j)) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
