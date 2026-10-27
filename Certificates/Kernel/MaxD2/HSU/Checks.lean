module

public import Certificates.Kernel.MaxD2.HSU.Enum
public import Certificates.Kernel.MaxD2.HSU.Data
public import Certificates.Kernel.MaxD2.HSP.Data
public import Certificates.Data.Kernel.MaxD2.Check
public import Certificates.Data.Kernel.MaxD2.Heis
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Data.HSFiveU35Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.HSU

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSU35

theorem k_xy : allN 2 (fun k => wordEqK 100 7 (mask 7) (pidn 100 7) HSP.GP HSP.GPI 2
    (uWords[k]!) (GP k)) = true := by quickRfl
theorem k_sz : szOK 100 7 = true := by quickRfl
theorem k_gp : allN 2 (fun k => permOK 100 7 (mask 7) (100 * 7) (GP k) (GPI k)) = true := by
  quickRfl
theorem n_sl0 : penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 0 500 = true := by quickRfl
theorem n_sl500 : penumSlK 100 7 (mask 7) (100 * 7) false NE.G NE.GI NE.k NE.cnt NE.T NE.PL
    NE.POS NE.SRT NE.SRI 500 500 = true := by quickRfl
theorem k_nh : penumHdK (pidn 100 7) NE.cnt dataU.nOrder NE.T NE.PL = true := by quickRfl
theorem k_ng : allN 3 (fun j => bAnd(wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2
    (dataU.nW[j]!) (NE.G j), canonK 100 7 (mask 7) (100 * 7) (NE.G j))) = true := by
  quickRfl
theorem k_ngi : allN 3 (fun j => permOK 100 7 (mask 7) (100 * 7) (NE.G j) (NGI j)) = true := by
  quickRfl
theorem k_r0 : Nat.beq (REP 0) (pidn 100 7) = true := by quickRfl
theorem k_rw : allN 1 (fun i => wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2
    (dataU.repW[i]!) (REP (Nat.succ i))) = true := by quickRfl
theorem k_ri : allN 2 (fun i => permOK 100 7 (mask 7) (100 * 7) (REP i) (REPI i)) = true := by
  quickRfl
theorem k_pts : allN 100 (fun t => bAnd(Nat.beq (dataU.fpPts[t]!) (r32 PT t),
    Nat.blt (r32 PT t) 100)) = true := by quickRfl
theorem k_srt : allN NE.cnt (sortK 7 100 700 NE.cnt (r32 PT) NE.T FS KS) = true := by quickRfl
theorem k_rep : repK 100 7 100 700 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H 1 = true := by
  quickRfl
theorem k_cnt : Nat.beq (posCnt NE.cnt H 1) (r32 CN 1) = true := by quickRfl
theorem k_rg0 : wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2 dataU.uW (RE.G 0) = true := by
  quickRfl
theorem k_rg1 : wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2 dataU.vW (RE.G 1) = true := by
  quickRfl
theorem k_rgc : allN 2 (fun j => canonK 100 7 (mask 7) (100 * 7) (RE.G j)) = true := by quickRfl
theorem k_rh : penumHdK (pidn 100 7) RE.cnt (dataU.p ^ 3) RE.T RE.PL = true := by quickRfl
theorem k_rsl : penumSlK 100 7 (mask 7) (100 * 7) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 125 = true := by quickRfl
theorem k_z : zK 100 7 RE.cnt dataU.p RE.T (r32 ZP) (r32 ZX) (RE.G 0) (RE.G 1) = true := by
  quickRfl
theorem k_uv : bIf(Nat.beq (pcomp 100 7 (mask 7) (RE.G 0) (RE.G 1))
    (pcomp 100 7 (mask 7) (RE.G 1) (RE.G 0)), false, true) = true := by quickRfl
theorem k_lab : labK 100 7 NE.k NE.G (r32 L) = true := by quickRfl
theorem k_mk : allN 2 (fun i => Nat.beq (rg 64 (mask 64) MK 0 i)
    (mkeyK 100 7 2 7 (r32 MISC 0) (r32 L) (REP i))) = true := by quickRfl
theorem k_sel : selK 2 (r32 MISC 1) (rg 64 (mask 64) MK 0)
    (fun i => nIf(Nat.beq i 0, NE.cnt, r32 CN i)) (fun _ => 0) (fun _ => 0) (fun _ => 0) =
    true := by quickRfl
theorem k_np0 : Nat.beq (r32 MISC 1) 0 = true := by quickRfl
theorem k_exp : allN RE.cnt (fun k => Nat.beq (pw 100 7 (RE.T k) dataU.p) (pidn 100 7)) =
    true := by quickRfl
theorem k_norm : allN 3 (fun j => allN 2 (fun i =>
    bAnd(conjInK 100 7 RE.cnt RE.T (NE.G j) (NGI j) (RE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 100 7 RE.cnt RE.T (NGI j) (NE.G j) (RE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_mvi : bAnd(Nat.blt (r32 MISC 3) 2, Nat.blt (r32 MISC 4) 2) = true := by quickRfl
theorem k_mv : notInK RE.cnt RE.T (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (GP (r32 MISC 3))
    (RE.G (r32 MISC 4))) (GPI (r32 MISC 3))) = true := by quickRfl
theorem k_tw : wordEqK 100 7 (mask 7) (pidn 100 7) GP GPI 2 dataU.tW (TT 0) = true := by
  quickRfl
theorem k_tp : permOK 100 7 (mask 7) (100 * 7) (TT 0) (TT 1) = true := by quickRfl
theorem k_th1 : Nat.blt (r32 MISC 2) NE.cnt = true := by quickRfl
theorem k_th2 : Nat.beq (NE.T (r32 MISC 2)) (TT 0) = true := by quickRfl
theorem k_tk : torusHK 100 7 dataU.p RE.cnt 5 dataU.tm dataU.tlam dataU.te RE.T (r32 ZP)
    (RE.G 0) (RE.G 1) (TT 0) (TT 1) = true := by quickRfl
theorem k_cent : allN NE.cnt (fun k => centK 100 7 RE.cnt NE.T RE.T (RE.G 0) (RE.G 1) (r32 CH k)
    k) = true := by quickRfl
theorem k_sum : Nat.beq ((List.range 2).foldl (fun s i => s + dataU.nOrder *
    dataU.nOrder / (if i = 0 then NE.cnt else r32 CN i)) 0) dataU.gOrder = true := by
  quickRfl
theorem k_gen : allN 1 (fun i => bAnd(Nat.beq (dataU.genW[i]!).length 2,
    allN 2 (fun j => wordEqK 100 7 (mask 7) (pidn 100 7)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, REP (Nat.succ i)))
      (fun l => nIf(Nat.blt l NE.k, NGI l, REPI (Nat.succ i))) 4
      ((dataU.genW[i]!)[j]!) (GP j)))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.HSU

end
