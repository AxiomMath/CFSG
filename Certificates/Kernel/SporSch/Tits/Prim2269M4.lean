module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mS0h : bAnd(Nat.blt 0 2925, bAnd(Nat.blt 1 2925, bAnd(Nat.blt 2923 4096, bAnd(Nat.blt 0 32,
    Nat.ble 2923 (Nat.mul 32 92))))) = true := by quickRfl
theorem mS0a : allN 2925 (fun y => Nat.beq (pgW 12 (TitsMS.A 0) y)
    (nIf(Nat.beq y 1, 0, y))) = true := by quickRfl
theorem mS0s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mS0s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mS0s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mS0s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mS0s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mS0s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mS0s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mS0s7 : allN 8 (fun t => bIf(Nat.blt (8 * 7 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 7 + t), true)) = true := by quickRfl
theorem mS0s8 : allN 8 (fun t => bIf(Nat.blt (8 * 8 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 8 + t), true)) = true := by quickRfl
theorem mS0s9 : allN 8 (fun t => bIf(Nat.blt (8 * 9 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 9 + t), true)) = true := by quickRfl
theorem mS0s10 : allN 8 (fun t => bIf(Nat.blt (8 * 10 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 10 + t), true)) = true := by quickRfl
theorem mS0s11 : allN 8 (fun t => bIf(Nat.blt (8 * 11 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)
      (8 * 11 + t), true)) = true := by quickRfl
theorem mS0s : allN 92 (segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s)) (recI 7012) (recU 2925 7012) (recV 2925 7012)) = true :=
  allN_chunks (B := 8) (C := 12) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mS0s0
    | 1, _ => exact mS0s1
    | 2, _ => exact mS0s2
    | 3, _ => exact mS0s3
    | 4, _ => exact mS0s4
    | 5, _ => exact mS0s5
    | 6, _ => exact mS0s6
    | 7, _ => exact mS0s7
    | 8, _ => exact mS0s8
    | 9, _ => exact mS0s9
    | 10, _ => exact mS0s10
    | 11, _ => exact mS0s11
theorem mS0t : allN 2925 (fun l => Nat.ble (pgW 12 (TitsMS.TP 0) l) 2923) = true := by quickRfl
theorem mS0c : Nat.beq (mergeCnt 2925 12 TitsSS.T 2923 32 (TitsMS.TP 0) (TitsMS.PP 0) (fun s => TitsMS.A (Nat.add 0 s))
    (recI 7012) (recU 2925 7012) (recV 2925 7012)) (timedCnt 2925 2923 (TitsMS.TP 0)) = true := by quickRfl
theorem mS0f : finalC 2925 12 2923 92 (TitsMS.TP 0) (fun s => TitsMS.A (Nat.add 0 s)) = true := by quickRfl
theorem mS0 : mergeCKG 2925 12 2 TitsSS.T 0 1 2923 32 92 (recI 7012) (recU 2925 7012) (recV 2925 7012) (TitsMS.TP 0) (TitsMS.PP 0)
    (fun s => TitsMS.A (Nat.add 0 s)) = true :=
  mergeCKG_of mS0h mS0a mS0s mS0t mS0c mS0f

end CertificateChecks.KernelSporSch.TitsPrim

end
