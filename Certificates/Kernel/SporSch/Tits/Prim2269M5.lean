module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mS1h : bAnd(Nat.blt 0 2925, bAnd(Nat.blt 7 2925, bAnd(Nat.blt 2923 4096, bAnd(Nat.blt 0 32,
    Nat.ble 2923 (Nat.mul 32 92))))) = true := by quickRfl
theorem mS1a : allN 2925 (fun y => Nat.beq (pgW 12 (TitsMS.A 128) y)
    (nIf(Nat.beq y 7, 0, y))) = true := by quickRfl
theorem mS1s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mS1s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mS1s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mS1s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mS1s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mS1s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mS1s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mS1s7 : allN 8 (fun t => bIf(Nat.blt (8 * 7 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 7 + t), true)) = true := by quickRfl
theorem mS1s8 : allN 8 (fun t => bIf(Nat.blt (8 * 8 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 8 + t), true)) = true := by quickRfl
theorem mS1s9 : allN 8 (fun t => bIf(Nat.blt (8 * 9 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 9 + t), true)) = true := by quickRfl
theorem mS1s10 : allN 8 (fun t => bIf(Nat.blt (8 * 10 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 10 + t), true)) = true := by quickRfl
theorem mS1s11 : allN 8 (fun t => bIf(Nat.blt (8 * 11 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)
      (8 * 11 + t), true)) = true := by quickRfl
theorem mS1s : allN 92 (segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s)) (recI 9935) (recU 2925 9935) (recV 2925 9935)) = true :=
  allN_chunks (B := 8) (C := 12) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mS1s0
    | 1, _ => exact mS1s1
    | 2, _ => exact mS1s2
    | 3, _ => exact mS1s3
    | 4, _ => exact mS1s4
    | 5, _ => exact mS1s5
    | 6, _ => exact mS1s6
    | 7, _ => exact mS1s7
    | 8, _ => exact mS1s8
    | 9, _ => exact mS1s9
    | 10, _ => exact mS1s10
    | 11, _ => exact mS1s11
theorem mS1t : allN 2925 (fun l => Nat.ble (pgW 12 (TitsMS.TP 1) l) 2923) = true := by quickRfl
theorem mS1c : Nat.beq (mergeCnt 2925 12 TitsSS.T 2923 32 (TitsMS.TP 1) (TitsMS.PP 1) (fun s => TitsMS.A (Nat.add 128 s))
    (recI 9935) (recU 2925 9935) (recV 2925 9935)) (timedCnt 2925 2923 (TitsMS.TP 1)) = true := by quickRfl
theorem mS1f : finalC 2925 12 2923 92 (TitsMS.TP 1) (fun s => TitsMS.A (Nat.add 128 s)) = true := by quickRfl
theorem mS1 : mergeCKG 2925 12 2 TitsSS.T 0 7 2923 32 92 (recI 9935) (recU 2925 9935) (recV 2925 9935) (TitsMS.TP 1) (TitsMS.PP 1)
    (fun s => TitsMS.A (Nat.add 128 s)) = true :=
  mergeCKG_of mS1h mS1a mS1s mS1t mS1c mS1f

end CertificateChecks.KernelSporSch.TitsPrim

end
