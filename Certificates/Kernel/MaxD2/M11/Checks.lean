module

public import Certificates.Kernel.MaxD2.M11.Enum
public import Certificates.Kernel.MaxD2.M11.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.M11ThreeLocal
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMaxD2.M11

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm

theorem k_sz : szOK 11 4 = true := by quickRfl
theorem k_gp : allN 2 (fun k => permOK 11 4 (mask 4) (11 * 4) (GP k) (GPI k)) = true := by quickRfl
theorem k_rg0 : wordEqK 11 4 (mask 4) (pidn 11 4) GP GPI 2 m11ThreeData.uW (RE.G 0) = true := by
  quickRfl
theorem k_rg1 : wordEqK 11 4 (mask 4) (pidn 11 4) GP GPI 2 m11ThreeData.vW (RE.G 1) = true := by
  quickRfl
theorem k_rgc : allN 2 (fun j => canonK 11 4 (mask 4) (11 * 4) (RE.G j)) = true := by quickRfl
theorem k_rh : penumHdK (pidn 11 4) RE.cnt (m11ThreeData.p ^ 2) RE.T RE.PL = true := by quickRfl
theorem k_rsl : penumSlK 11 4 (mask 4) (11 * 4) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 9 = true := by quickRfl
theorem k_nh : penumHdK (pidn 11 4) NE.cnt m11ThreeData.nOrder NE.T NE.PL = true := by quickRfl
theorem k_nsl : penumSlK 11 4 (mask 4) (11 * 4) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 0 144 = true := by quickRfl
theorem k_ng : allN 5 (fun j => bAnd(wordEqK 11 4 (mask 4) (pidn 11 4) GP GPI 2
    (m11ThreeData.nW[j]!) (NE.G j), canonK 11 4 (mask 4) (11 * 4) (NE.G j))) = true := by
  quickRfl
theorem k_ngi : allN 5 (fun j => permOK 11 4 (mask 4) (11 * 4) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_norm : allN 5 (fun j => allN 2 (fun i =>
    bAnd(conjInK 11 4 RE.cnt RE.T (NE.G j) (NGI j) (RE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 11 4 RE.cnt RE.T (NGI j) (NE.G j) (RE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_mv : notInK RE.cnt RE.T (pcomp 11 4 (mask 4) (pcomp 11 4 (mask 4) (GP 0) (RE.G 0))
    (GPI 0)) = true := by quickRfl
theorem k_tw : wordEqK 11 4 (mask 4) (pidn 11 4) GP GPI 2 m11ThreeData.tW (TT 0) = true := by
  quickRfl
theorem k_tp : permOK 11 4 (mask 4) (11 * 4) (TT 0) (TT 1) = true := by quickRfl
theorem k_th1 : Nat.blt (r32 MISC 0) NE.cnt = true := by quickRfl
theorem k_th2 : Nat.beq (NE.T (r32 MISC 0)) (TT 0) = true := by quickRfl
theorem k_tk : torusK 11 4 m11ThreeData.p RE.cnt m11ThreeData.tm m11ThreeData.tlam m11ThreeData.te
    RE.T (TT 0) (TT 1) = true := by quickRfl
theorem k_cent : allN NE.cnt (fun k => centK 11 4 RE.cnt NE.T RE.T (RE.G 0) (RE.G 1) (r32 CH k) k) =
    true := by quickRfl
theorem k_r0 : Nat.beq (REP 0) (pidn 11 4) = true := by quickRfl
theorem k_rw : allN 2 (fun i => wordEqK 11 4 (mask 4) (pidn 11 4) GP GPI 2
    (m11ThreeData.repW[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 3 (fun i => permOK 11 4 (mask 4) (11 * 4) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 4 (fun t => bAnd(Nat.beq (m11ThreeData.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 11)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 4 4 16 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_test : allN 2 (fun d => repK 11 4 4 16 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.succ d)) = true := by quickRfl
theorem k_cnt : allN 2 (fun i => Nat.beq (posCnt NE.cnt H (Nat.succ i)) (r32 CN (Nat.succ i))) =
    true := by quickRfl
theorem k_sum : Nat.beq ((List.range 3).foldl (fun s i => s + m11ThreeData.nOrder *
    m11ThreeData.nOrder / (if i = 0 then NE.cnt else r32 CN i)) 0) m11ThreeData.gOrder = true := by
  quickRfl
theorem k_lab : labK 11 4 NE.k NE.G (r32 L) = true := by quickRfl
theorem k_mk : allN 3 (fun i => Nat.beq (rg 64 (mask 64) MK 0 i)
    (mkeyK 11 4 1 4 (r32 MISC 1) (r32 L) (REP i))) = true := by quickRfl
theorem k_mkd : allN 3 (fun i => allN 3 (fun j => bIf(Nat.blt i j,
    bIf(Nat.beq (rg 64 (mask 64) MK 0 i) (rg 64 (mask 64) MK 0 j), false, true), true))) =
    true := by quickRfl
theorem k_gen : allN 2 (fun i => bAnd(Nat.beq (m11ThreeData.genW[i]!).length 2,
    allN 2 (fun j => wordEqK 11 4 (mask 4) (pidn 11 4)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, REP (Nat.succ i)))
      (fun l => nIf(Nat.blt l NE.k, NGI l, REPI (Nat.succ i))) 6
      ((m11ThreeData.genW[i]!)[j]!) (GP j)))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.M11

end
