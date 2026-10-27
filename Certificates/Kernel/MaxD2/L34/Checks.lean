module

public import Certificates.Kernel.MaxD2.L34.Enum
public import Certificates.Kernel.MaxD2.L34.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.MaxD2.Pair
public import Certificates.Data.L34InnerLocal
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.L34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm

theorem k_sz : szOK 42 6 = true := by quickRfl
theorem k_gp : allN 3 (fun k => permOK 42 6 (mask 6) (42 * 6) (GP k) (GPI k)) = true := by quickRfl
theorem k_rg0 : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3 l34InnerData.uW (RE.G 0) = true := by
  quickRfl
theorem k_rg1 : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3 l34InnerData.vW (RE.G 1) = true := by
  quickRfl
theorem k_rgc : allN 2 (fun j => canonK 42 6 (mask 6) (42 * 6) (RE.G j)) = true := by quickRfl
theorem k_rh : penumHdK (pidn 42 6) RE.cnt (l34InnerData.p ^ 2) RE.T RE.PL = true := by quickRfl
theorem k_rsl : penumSlK 42 6 (mask 6) (42 * 6) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 9 = true := by quickRfl
theorem k_nh : penumHdK (pidn 42 6) NE.cnt l34InnerData.nOrder NE.T NE.PL = true := by quickRfl
theorem k_nsl : penumSlK 42 6 (mask 6) (42 * 6) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 0 72 = true := by quickRfl
theorem k_ng : allN 3 (fun j => bAnd(wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3
    (l34InnerData.nW[j]!) (NE.G j), canonK 42 6 (mask 6) (42 * 6) (NE.G j))) = true := by
  quickRfl
theorem k_ngi : allN 3 (fun j => permOK 42 6 (mask 6) (42 * 6) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_norm : allN 3 (fun j => allN 2 (fun i =>
    bAnd(conjInK 42 6 RE.cnt RE.T (NE.G j) (NGI j) (RE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 42 6 RE.cnt RE.T (NGI j) (NE.G j) (RE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_mv : notInK RE.cnt RE.T (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (GP 0) (RE.G 0))
    (GPI 0)) = true := by quickRfl
theorem k_tw : wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3 l34InnerData.tW (TT 0) = true := by
  quickRfl
theorem k_tp : permOK 42 6 (mask 6) (42 * 6) (TT 0) (TT 1) = true := by quickRfl
theorem k_th1 : Nat.blt (r32 MISC 0) NE.cnt = true := by quickRfl
theorem k_th2 : Nat.beq (NE.T (r32 MISC 0)) (TT 0) = true := by quickRfl
theorem k_tk : torusK 42 6 l34InnerData.p RE.cnt l34InnerData.tm l34InnerData.tlam l34InnerData.te
    RE.T (TT 0) (TT 1) = true := by quickRfl
theorem k_cent : allN NE.cnt (fun k => centK 42 6 RE.cnt NE.T RE.T (RE.G 0) (RE.G 1) (r32 CH k) k) =
    true := by quickRfl
theorem k_r0 : Nat.beq (REP 0) (pidn 42 6) = true := by quickRfl
theorem k_rw : allN 7 (fun i => wordEqK 42 6 (mask 6) (pidn 42 6) GP GPI 3
    (l34InnerData.repW[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 8 (fun i => permOK 42 6 (mask 6) (42 * 6) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 2 (fun t => bAnd(Nat.beq (l34InnerData.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 42)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 6 2 12 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_test : allN 7 (fun d => repK 42 6 2 12 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.succ d)) = true := by quickRfl
theorem k_cnt : allN 7 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 8).foldl (fun s i => s + l34InnerData.nOrder *
    l34InnerData.nOrder / (if i = 0 then NE.cnt else r32 CN i)) 0) l34InnerData.gOrder = true := by
  quickRfl
theorem k_lab : labK 42 6 NE.k NE.G (r32 L) = true := by quickRfl
theorem k_mk : allN 8 (fun i => Nat.beq (rg 128 (mask 128) MK 0 i)
    (mkeyK 42 6 1 6 (r32 MISC 1) (r32 L) (REP i))) = true := by quickRfl
theorem k_pair : allN 8 (fun i => allN 8 (fun j => bIf(Nat.blt i j,
    pairK 42 6 2 12 NE.cnt (r32 PT) NE.T FS KS REP REPI RB2 H2
      (Nat.add (Nat.div (Nat.mul j (Nat.sub j 1)) 2) i) i j, true))) = true := by quickRfl
theorem k_gen : allN 7 (fun i => bAnd(Nat.beq (l34InnerData.genW[i]!).length 3,
    allN 3 (fun j => wordEqK 42 6 (mask 6) (pidn 42 6)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, REP (Nat.succ i)))
      (fun l => nIf(Nat.blt l NE.k, NGI l, REPI (Nat.succ i))) 4
      ((l34InnerData.genW[i]!)[j]!) (GP j)))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.L34

end
