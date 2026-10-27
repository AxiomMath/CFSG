module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mO0h : bAnd(Nat.blt 0 1755, bAnd(Nat.blt 1 1755, bAnd(Nat.blt 1753 4096, bAnd(Nat.blt 0 32,
    Nat.ble 1753 (Nat.mul 32 55))))) = true := by quickRfl
theorem mO0a : allN 1755 (fun y => Nat.beq (pgW 11 (TitsMO.A 0) y)
    (nIf(Nat.beq y 1, 0, y))) = true := by quickRfl
theorem mO0s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mO0s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mO0s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mO0s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mO0s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mO0s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mO0s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mO0s : allN 55 (segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s)) (recI 0) (recU 1755 0) (recV 1755 0)) = true :=
  allN_chunks (B := 8) (C := 7) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mO0s0
    | 1, _ => exact mO0s1
    | 2, _ => exact mO0s2
    | 3, _ => exact mO0s3
    | 4, _ => exact mO0s4
    | 5, _ => exact mO0s5
    | 6, _ => exact mO0s6
theorem mO0t : allN 1755 (fun l => Nat.ble (pgW 12 (TitsMO.TP 0) l) 1753) = true := by quickRfl
theorem mO0c : Nat.beq (mergeCnt 1755 11 TitsSD.T 1753 32 (TitsMO.TP 0) (TitsMO.PP 0) (fun s => TitsMO.A (Nat.add 0 s))
    (recI 0) (recU 1755 0) (recV 1755 0)) (timedCnt 1755 1753 (TitsMO.TP 0)) = true := by quickRfl
theorem mO0f : finalC 1755 11 1753 55 (TitsMO.TP 0) (fun s => TitsMO.A (Nat.add 0 s)) = true := by quickRfl
theorem mO0 : mergeCKG 1755 11 2 TitsSD.T 0 1 1753 32 55 (recI 0) (recU 1755 0) (recV 1755 0) (TitsMO.TP 0) (TitsMO.PP 0)
    (fun s => TitsMO.A (Nat.add 0 s)) = true :=
  mergeCKG_of mO0h mO0a mO0s mO0t mO0c mO0f

end CertificateChecks.KernelSporSch.TitsPrim

end
