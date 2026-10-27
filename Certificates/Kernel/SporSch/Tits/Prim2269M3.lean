module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mO3h : bAnd(Nat.blt 0 1755, bAnd(Nat.blt 87 1755, bAnd(Nat.blt 1753 4096, bAnd(Nat.blt 0 32,
    Nat.ble 1753 (Nat.mul 32 55))))) = true := by quickRfl
theorem mO3a : allN 1755 (fun y => Nat.beq (pgW 11 (TitsMO.A 384) y)
    (nIf(Nat.beq y 87, 0, y))) = true := by quickRfl
theorem mO3s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mO3s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mO3s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mO3s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mO3s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mO3s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mO3s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mO3s : allN 55 (segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s)) (recI 5259) (recU 1755 5259) (recV 1755 5259)) = true :=
  allN_chunks (B := 8) (C := 7) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mO3s0
    | 1, _ => exact mO3s1
    | 2, _ => exact mO3s2
    | 3, _ => exact mO3s3
    | 4, _ => exact mO3s4
    | 5, _ => exact mO3s5
    | 6, _ => exact mO3s6
theorem mO3t : allN 1755 (fun l => Nat.ble (pgW 12 (TitsMO.TP 3) l) 1753) = true := by quickRfl
theorem mO3c : Nat.beq (mergeCnt 1755 11 TitsSD.T 1753 32 (TitsMO.TP 3) (TitsMO.PP 3) (fun s => TitsMO.A (Nat.add 384 s))
    (recI 5259) (recU 1755 5259) (recV 1755 5259)) (timedCnt 1755 1753 (TitsMO.TP 3)) = true := by quickRfl
theorem mO3f : finalC 1755 11 1753 55 (TitsMO.TP 3) (fun s => TitsMO.A (Nat.add 384 s)) = true := by quickRfl
theorem mO3 : mergeCKG 1755 11 2 TitsSD.T 0 87 1753 32 55 (recI 5259) (recU 1755 5259) (recV 1755 5259) (TitsMO.TP 3) (TitsMO.PP 3)
    (fun s => TitsMO.A (Nat.add 384 s)) = true :=
  mergeCKG_of mO3h mO3a mO3s mO3t mO3c mO3f

end CertificateChecks.KernelSporSch.TitsPrim

end
