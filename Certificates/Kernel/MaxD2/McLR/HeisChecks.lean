module

public import Certificates.Kernel.MaxD2.McLR.Enum
public import Certificates.Kernel.MaxD2.McLR.Data
public import Certificates.Kernel.MaxD2.McLR.HeisEnum
public import Certificates.Kernel.MaxD2.McLR.HeisData
public import Certificates.Data.Kernel.MaxD2.Heis
public import Certificates.Data.McLFiveLocalR
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MaxD2 CFSG.KS.PEnum CFSG.KS.Row
open Certificates.MaxD2Perm Certificates.MaxD2Heis

theorem k_rg0 : wordEqK 275 9 (mask 9) (pidn 275 9) GP GPI 3 mclFiveDataR.uW (RE.G 0) = true := by
  quickRfl
theorem k_rg1 : wordEqK 275 9 (mask 9) (pidn 275 9) GP GPI 3 mclFiveDataR.vW (RE.G 1) = true := by
  quickRfl
theorem k_rgc : allN 2 (fun j => canonK 275 9 (mask 9) (275 * 9) (RE.G j)) = true := by quickRfl
theorem k_rh : penumHdK (pidn 275 9) RE.cnt (mclFiveDataR.p ^ 3) RE.T RE.PL = true := by quickRfl
theorem k_rsl : penumSlK 275 9 (mask 9) (275 * 9) false RE.G RE.GI RE.k RE.cnt RE.T RE.PL
    RE.POS RE.SRT RE.SRI 0 125 = true := by quickRfl
theorem k_z : zK 275 9 RE.cnt mclFiveDataR.p RE.T (r32 ZP) (r32 ZX) (RE.G 0) (RE.G 1) = true := by
  quickRfl
theorem k_uv : bIf(Nat.beq (pcomp 275 9 (mask 9) (RE.G 0) (RE.G 1))
    (pcomp 275 9 (mask 9) (RE.G 1) (RE.G 0)), false, true) = true := by quickRfl
theorem k_lab : labK 275 9 NE.k NE.G (r32 L) = true := by quickRfl
theorem k_mk : allN 69 (fun i => Nat.beq (rg 64 (mask 64) MK 0 i)
    (mkeyK 275 9 5 9 (r32 MISC 0) (r32 L) (REP i))) = true := by quickRfl
theorem k_sel : selK 69 (r32 MISC 1) (rg 64 (mask 64) MK 0)
    (fun i => nIf(Nat.beq i 0, NE.cnt, r32 CN i)) (r32 PQ) (r32 PI) (r32 PJ) = true := by quickRfl
theorem k_exp : allN RE.cnt (fun k => Nat.beq (pw 275 9 (RE.T k) mclFiveDataR.p) (pidn 275 9)) =
    true := by quickRfl
theorem k_norm : allN 5 (fun j => allN 2 (fun i =>
    bAnd(conjInK 275 9 RE.cnt RE.T (NE.G j) (NGI j) (RE.G i)
      (r32 NH (Nat.add (Nat.mul 4 j) (Nat.mul 2 i))),
    conjInK 275 9 RE.cnt RE.T (NGI j) (NE.G j) (RE.G i)
      (r32 NH (Nat.add (Nat.add (Nat.mul 4 j) (Nat.mul 2 i)) 1))))) = true := by quickRfl
theorem k_mvi : bAnd(Nat.blt (r32 MISC 3) 3, Nat.blt (r32 MISC 4) 2) = true := by quickRfl
theorem k_mv : notInK RE.cnt RE.T (pcomp 275 9 (mask 9) (pcomp 275 9 (mask 9) (GP (r32 MISC 3))
    (RE.G (r32 MISC 4))) (GPI (r32 MISC 3))) = true := by quickRfl
theorem k_tw : wordEqK 275 9 (mask 9) (pidn 275 9) GP GPI 3 mclFiveDataR.tW (TT 0) = true := by
  quickRfl
theorem k_tp : permOK 275 9 (mask 9) (275 * 9) (TT 0) (TT 1) = true := by quickRfl
theorem k_th1 : Nat.blt (r32 MISC 2) NE.cnt = true := by quickRfl
theorem k_th2 : Nat.beq (NE.T (r32 MISC 2)) (TT 0) = true := by quickRfl
theorem k_tk : torusHK 275 9 mclFiveDataR.p RE.cnt 5 mclFiveDataR.tm mclFiveDataR.tlam
    mclFiveDataR.te RE.T (r32 ZP) (RE.G 0) (RE.G 1) (TT 0) (TT 1) = true := by quickRfl
theorem k_cent : allN NE.cnt (fun k => centK 275 9 RE.cnt NE.T RE.T (RE.G 0) (RE.G 1) (r32 CH k)
    k) = true := by quickRfl
theorem k_sum : Nat.beq ((List.range 69).foldl (fun s i => s + mclFiveDataR.nOrder *
    mclFiveDataR.nOrder / (if i = 0 then NE.cnt else r32 CN i)) 0) mclFiveDataR.gOrder = true := by
  quickRfl
theorem k_gen : allN 68 (fun i => bAnd(Nat.beq (mclFiveDataR.genW[i]!).length 3,
    allN 3 (fun j => wordEqK 275 9 (mask 9) (pidn 275 9)
      (fun l => nIf(Nat.blt l NE.k, NE.G l, REP (Nat.succ i)))
      (fun l => nIf(Nat.blt l NE.k, NGI l, REPI (Nat.succ i))) 6
      ((mclFiveDataR.genW[i]!)[j]!) (GP j)))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.McLR

end
