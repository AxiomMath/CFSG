module

public import Certificates.Kernel.TitsOver.Three.SEnum1
public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Kernel.TitsOver.Three.Loc1Data
public import Certificates.Data.Kernel.MaxD2.Check
public import CFSG.LocalAnalysis.StandardType.TitsThreeOvergroupData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open CFSG.StandardType.TitsThree

theorem c1_rg : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 6
    ((Certificates.MaxD2Perm.rWs (lLocalData 1 ()))[j]!) (C1RE.G j),
    canonK 1755 11 (mask 11) (1755 * 11) (C1RE.G j))) = true := by quickRfl
theorem c1_rh : penumHdK (pidn 1755 11) C1RE.cnt 9 C1RE.T C1RE.PL = true := by quickRfl
theorem c1_rsl : penumSlK 1755 11 (mask 11) (1755 * 11) false C1RE.G C1RE.GI C1RE.k C1RE.cnt C1RE.T
    C1RE.PL C1RE.POS C1RE.SRT C1RE.SRI 0 9 = true := by quickRfl
theorem c1_nh : penumHdK (pidn 1755 11) C1NE.cnt 432 C1NE.T C1NE.PL = true := by quickRfl
theorem c1_ng : allN 2 (fun j => bAnd(wordEqK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 6
    ((lLocalData 1 ()).nW[j]!) (C1NE.G j), canonK 1755 11 (mask 11) (1755 * 11) (C1NE.G j))) =
    true := by quickRfl
theorem c1_ngi : allN 2 (fun j => permOK 1755 11 (mask 11) (1755 * 11) (C1NE.G j) (C1NGI j)) =
    true := by quickRfl
theorem c1_norm : allN 2 (fun j => allN 2 (fun i =>
    bAnd(conjInK 1755 11 C1RE.cnt C1RE.T (C1NE.G j) (C1NGI j) (C1RE.G i)
      (r32 C1NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 1755 11 C1RE.cnt C1RE.T (C1NGI j) (C1NE.G j) (C1RE.G i)
      (r32 C1NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem c1_mv : notInK C1RE.cnt C1RE.T (pcomp 1755 11 (mask 11) (pcomp 1755 11 (mask 11) (S1E.G 3)
    (C1RE.G 0)) (SGI1 3)) = true := by quickRfl
theorem c1_tw : wordEqK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 6 (lLocalData 1 ()).tW (C1TT 0) =
    true := by quickRfl
theorem c1_tp : permOK 1755 11 (mask 11) (1755 * 11) (C1TT 0) (C1TT 1) = true := by quickRfl
theorem c1_th1 : Nat.blt (r32 C1MISC 0) C1NE.cnt = true := by quickRfl
theorem c1_th2 : Nat.beq (C1NE.T (r32 C1MISC 0)) (C1TT 0) = true := by quickRfl
theorem c1_tk : torusK 1755 11 3 C1RE.cnt 4 2 4 C1RE.T (C1TT 0) (C1TT 1) = true := by quickRfl
theorem c1_cent : allN C1NE.cnt (fun k => centK 1755 11 C1RE.cnt C1NE.T C1RE.T (C1RE.G 0) (C1RE.G 1)
    (r32 C1CH k) k) = true := by quickRfl
theorem c1_r0 : Nat.beq (C1REP 0) (pidn 1755 11) = true := by quickRfl
theorem c1_rw : wordEqK 1755 11 (mask 11) (pidn 1755 11) S1E.G SGI1 6 ((lLocalData 1 ()).repW[0]!)
    (C1REP 1) = true := by quickRfl
theorem c1_ri : allN 2 (fun i => permOK 1755 11 (mask 11) (1755 * 11) (C1REP i) (C1REPI i)) = true := by
  quickRfl
theorem c1_pts : allN 2 (fun t => bAnd(Nat.beq ((lLocalData 1 ()).fpPts[t]!) (r32 C1PT t),
    Nat.blt (r32 C1PT t) 1755)) = true := by quickRfl
theorem c1_srt : allN C1NE.cnt (sortK 11 2 22 C1NE.cnt (r32 C1PT) C1NE.T C1FS C1KS) = true := by
  quickRfl
theorem c1_test : repK 1755 11 2 22 C1NE.cnt (r32 C1PT) C1NE.T C1FS C1KS C1REP C1REPI C1RB C1H 1 =
    true := by quickRfl
theorem c1_cnt : Nat.beq (posCnt C1NE.cnt C1H 1) (r32 C1CN 1) = true := by quickRfl
theorem c1_sum : Nat.beq ((List.range 2).foldl (fun s i => s + 432 * 432 /
    (if i = 0 then C1NE.cnt else r32 C1CN i)) 0) 5616 = true := by quickRfl
theorem c1_lab : labK 1755 11 C1NE.k C1NE.G (r32 C1L) = true := by quickRfl
theorem c1_mk : allN 2 (fun i => Nat.beq (rg 1024 (mask 1024) C1MK 0 i)
    (mkeyK 1755 11 28 11 (r32 C1MISC 1) (r32 C1L) (C1REP i))) = true := by quickRfl
theorem c1_mkd : (Nat.beq (rg 1024 (mask 1024) C1MK 0 0) (rg 1024 (mask 1024) C1MK 0 1)).not =
    true := by quickRfl
theorem c1_gen1 : Nat.beq ((lLocalData 1 ()).genW[0]!).length 6 = true := by quickRfl
theorem c1_gen2 : allN 6 (fun j => wordEqK 1755 11 (mask 11) (pidn 1755 11)
    (fun l => nIf(Nat.blt l C1NE.k, C1NE.G l, C1REP 1))
    (fun l => nIf(Nat.blt l C1NE.k, C1NGI l, C1REPI 1)) 3
    (((lLocalData 1 ()).genW[0]!)[j]!) (S1E.G j)) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
