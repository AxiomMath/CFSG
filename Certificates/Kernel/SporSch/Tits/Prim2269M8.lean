module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mS4h : bAnd(Nat.blt 0 2925, bAnd(Nat.blt 141 2925, bAnd(Nat.blt 2923 4096, bAnd(Nat.blt 0 32,
    Nat.ble 2923 (Nat.mul 32 92))))) = true := by quickRfl
theorem mS4a : allN 2925 (fun y => Nat.beq (pgW 12 (TitsMS.A 512) y)
    (nIf(Nat.beq y 141, 0, y))) = true := by quickRfl
theorem mS4s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mS4s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mS4s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mS4s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mS4s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mS4s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mS4s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mS4s7 : allN 8 (fun t => bIf(Nat.blt (8 * 7 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 7 + t), true)) = true := by quickRfl
theorem mS4s8 : allN 8 (fun t => bIf(Nat.blt (8 * 8 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 8 + t), true)) = true := by quickRfl
theorem mS4s9 : allN 8 (fun t => bIf(Nat.blt (8 * 9 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 9 + t), true)) = true := by quickRfl
theorem mS4s10 : allN 8 (fun t => bIf(Nat.blt (8 * 10 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 10 + t), true)) = true := by quickRfl
theorem mS4s11 : allN 8 (fun t => bIf(Nat.blt (8 * 11 + t) 92,
    segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)
      (8 * 11 + t), true)) = true := by quickRfl
theorem mS4s : allN 92 (segCG 2925 12 2 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s)) (recI 18704) (recU 2925 18704) (recV 2925 18704)) = true :=
  allN_chunks (B := 8) (C := 12) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mS4s0
    | 1, _ => exact mS4s1
    | 2, _ => exact mS4s2
    | 3, _ => exact mS4s3
    | 4, _ => exact mS4s4
    | 5, _ => exact mS4s5
    | 6, _ => exact mS4s6
    | 7, _ => exact mS4s7
    | 8, _ => exact mS4s8
    | 9, _ => exact mS4s9
    | 10, _ => exact mS4s10
    | 11, _ => exact mS4s11
theorem mS4t : allN 2925 (fun l => Nat.ble (pgW 12 (TitsMS.TP 4) l) 2923) = true := by quickRfl
theorem mS4c : Nat.beq (mergeCnt 2925 12 TitsSS.T 2923 32 (TitsMS.TP 4) (TitsMS.PP 4) (fun s => TitsMS.A (Nat.add 512 s))
    (recI 18704) (recU 2925 18704) (recV 2925 18704)) (timedCnt 2925 2923 (TitsMS.TP 4)) = true := by quickRfl
theorem mS4f : finalC 2925 12 2923 92 (TitsMS.TP 4) (fun s => TitsMS.A (Nat.add 512 s)) = true := by quickRfl
theorem mS4 : mergeCKG 2925 12 2 TitsSS.T 0 141 2923 32 92 (recI 18704) (recU 2925 18704) (recV 2925 18704) (TitsMS.TP 4) (TitsMS.PP 4)
    (fun s => TitsMS.A (Nat.add 512 s)) = true :=
  mergeCKG_of mS4h mS4a mS4s mS4t mS4c mS4f

end CertificateChecks.KernelSporSch.TitsPrim

end
