module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mO1h : bAnd(Nat.blt 0 1755, bAnd(Nat.blt 6 1755, bAnd(Nat.blt 1753 4096, bAnd(Nat.blt 0 32,
    Nat.ble 1753 (Nat.mul 32 55))))) = true := by quickRfl
theorem mO1a : allN 1755 (fun y => Nat.beq (pgW 11 (TitsMO.A 128) y)
    (nIf(Nat.beq y 6, 0, y))) = true := by quickRfl
theorem mO1s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mO1s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mO1s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mO1s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mO1s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mO1s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mO1s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mO1s : allN 55 (segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s)) (recI 1753) (recU 1755 1753) (recV 1755 1753)) = true :=
  allN_chunks (B := 8) (C := 7) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mO1s0
    | 1, _ => exact mO1s1
    | 2, _ => exact mO1s2
    | 3, _ => exact mO1s3
    | 4, _ => exact mO1s4
    | 5, _ => exact mO1s5
    | 6, _ => exact mO1s6
theorem mO1t : allN 1755 (fun l => Nat.ble (pgW 12 (TitsMO.TP 1) l) 1753) = true := by quickRfl
theorem mO1c : Nat.beq (mergeCnt 1755 11 TitsSD.T 1753 32 (TitsMO.TP 1) (TitsMO.PP 1) (fun s => TitsMO.A (Nat.add 128 s))
    (recI 1753) (recU 1755 1753) (recV 1755 1753)) (timedCnt 1755 1753 (TitsMO.TP 1)) = true := by quickRfl
theorem mO1f : finalC 1755 11 1753 55 (TitsMO.TP 1) (fun s => TitsMO.A (Nat.add 128 s)) = true := by quickRfl
theorem mO1 : mergeCKG 1755 11 2 TitsSD.T 0 6 1753 32 55 (recI 1753) (recU 1755 1753) (recV 1755 1753) (TitsMO.TP 1) (TitsMO.PP 1)
    (fun s => TitsMO.A (Nat.add 128 s)) = true :=
  mergeCKG_of mO1h mO1a mO1s mO1t mO1c mO1f

end CertificateChecks.KernelSporSch.TitsPrim

end
