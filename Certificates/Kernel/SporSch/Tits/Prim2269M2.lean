module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mO2h : bAnd(Nat.blt 0 1755, bAnd(Nat.blt 24 1755, bAnd(Nat.blt 1753 4096, bAnd(Nat.blt 0 32,
    Nat.ble 1753 (Nat.mul 32 55))))) = true := by quickRfl
theorem mO2a : allN 1755 (fun y => Nat.beq (pgW 11 (TitsMO.A 256) y)
    (nIf(Nat.beq y 24, 0, y))) = true := by quickRfl
theorem mO2s0 : allN 8 (fun t => bIf(Nat.blt (8 * 0 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 0 + t), true)) = true := by quickRfl
theorem mO2s1 : allN 8 (fun t => bIf(Nat.blt (8 * 1 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 1 + t), true)) = true := by quickRfl
theorem mO2s2 : allN 8 (fun t => bIf(Nat.blt (8 * 2 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 2 + t), true)) = true := by quickRfl
theorem mO2s3 : allN 8 (fun t => bIf(Nat.blt (8 * 3 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 3 + t), true)) = true := by quickRfl
theorem mO2s4 : allN 8 (fun t => bIf(Nat.blt (8 * 4 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 4 + t), true)) = true := by quickRfl
theorem mO2s5 : allN 8 (fun t => bIf(Nat.blt (8 * 5 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 5 + t), true)) = true := by quickRfl
theorem mO2s6 : allN 8 (fun t => bIf(Nat.blt (8 * 6 + t) 55,
    segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)
      (8 * 6 + t), true)) = true := by quickRfl
theorem mO2s : allN 55 (segCG 1755 11 2 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s)) (recI 3506) (recU 1755 3506) (recV 1755 3506)) = true :=
  allN_chunks (B := 8) (C := 7) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mO2s0
    | 1, _ => exact mO2s1
    | 2, _ => exact mO2s2
    | 3, _ => exact mO2s3
    | 4, _ => exact mO2s4
    | 5, _ => exact mO2s5
    | 6, _ => exact mO2s6
theorem mO2t : allN 1755 (fun l => Nat.ble (pgW 12 (TitsMO.TP 2) l) 1753) = true := by quickRfl
theorem mO2c : Nat.beq (mergeCnt 1755 11 TitsSD.T 1753 32 (TitsMO.TP 2) (TitsMO.PP 2) (fun s => TitsMO.A (Nat.add 256 s))
    (recI 3506) (recU 1755 3506) (recV 1755 3506)) (timedCnt 1755 1753 (TitsMO.TP 2)) = true := by quickRfl
theorem mO2f : finalC 1755 11 1753 55 (TitsMO.TP 2) (fun s => TitsMO.A (Nat.add 256 s)) = true := by quickRfl
theorem mO2 : mergeCKG 1755 11 2 TitsSD.T 0 24 1753 32 55 (recI 3506) (recU 1755 3506) (recV 1755 3506) (TitsMO.TP 2) (TitsMO.PP 2)
    (fun s => TitsMO.A (Nat.add 256 s)) = true :=
  mergeCKG_of mO2h mO2a mO2s mO2t mO2c mO2f

end CertificateChecks.KernelSporSch.TitsPrim

end
