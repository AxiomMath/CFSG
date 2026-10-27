module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mS3h : bAnd(Nat.blt 0 2925, bAnd(Nat.blt 107 2925, bAnd(Nat.blt 2923 4096, bAnd(Nat.blt 0 32,
    Nat.ble 2923 (Nat.mul 32 92))))) = true := by quickRfl
theorem mS3a : allN 2925 (fun y => Nat.beq (pgW 12 (TitsMS.A 384) y)
    (nIf(Nat.beq y 107, 0, y))) = true := by quickRfl
theorem mS3s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mS3s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mS3s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mS3s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mS3s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mS3s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mS3s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mS3s7 : allN 8 (fun t => bIf(Nat.blt (8 * 7 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 7 + t), true)) = true := by quickRfl
theorem mS3s8 : allN 8 (fun t => bIf(Nat.blt (8 * 8 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 8 + t), true)) = true := by quickRfl
theorem mS3s9 : allN 8 (fun t => bIf(Nat.blt (8 * 9 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 9 + t), true)) = true := by quickRfl
theorem mS3s10 : allN 8 (fun t => bIf(Nat.blt (8 * 10 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 10 + t), true)) = true := by quickRfl
theorem mS3s11 : allN 8 (fun t => bIf(Nat.blt (8 * 11 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (8 * 11 + t), true)) = true := by quickRfl
theorem mS3s : allN 92 (segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)) = true :=
  allN_chunks (B := 8) (C := 12) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mS3s0
    | 1, _ => exact mS3s1
    | 2, _ => exact mS3s2
    | 3, _ => exact mS3s3
    | 4, _ => exact mS3s4
    | 5, _ => exact mS3s5
    | 6, _ => exact mS3s6
    | 7, _ => exact mS3s7
    | 8, _ => exact mS3s8
    | 9, _ => exact mS3s9
    | 10, _ => exact mS3s10
    | 11, _ => exact mS3s11
theorem mS3t : allN 2925 (fun l => Nat.ble (pgW 12 (TitsMS.TP 3) l) 2923) = true := by quickRfl
theorem mS3c : Nat.beq (mergeCnt 2925 12 TitsSS.T 2923 32 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
    (recI 15781) (recU 2925 15781) (recV 2925 15781)) (timedCnt 2925 2923 (TitsMS.TP 3)) = true := by quickRfl
theorem mS3f : finalC 2925 12 2923 92 (TitsMS.TP 3) (fun s => TitsMS.A (Nat.add 384 s)) = true := by quickRfl
theorem mS3 : mergeCKG 2925 12 2 TitsSS.T 0 107 2923 32 92 (recI 15781) (recU 2925 15781) (recV 2925 15781) (TitsMS.TP 3) (TitsMS.PP 3)
    (fun s => TitsMS.A (Nat.add 384 s)) = true :=
  mergeCKG_of mS3h mS3a mS3s mS3t mS3c mS3f

end CertificateChecks.KernelSporSch.TitsPrim

end
