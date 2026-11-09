module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mS3h : bAnd(Nat.blt 0 2925, bAnd(Nat.blt 107 2925, bAnd(Nat.blt 2923 4096, bAnd(Nat.blt 0 128,
    Nat.ble 2923 (Nat.mul 128 23))))) = true := by quickRfl
theorem mS3a : allN 2925 (fun y => Nat.beq (pgW 12 (TitsMS.A 384) y)
    (nIf(Nat.beq y 107, 0, y))) = true := by quickRfl
theorem mS3s0 : allN 4 (fun t => bIf(Nat.blt (4 * 0 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
      (fun s => TitsMS.M (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (4 * 0 + t), true)) = true := by quickRfl
theorem mS3s1 : allN 4 (fun t => bIf(Nat.blt (4 * 1 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
      (fun s => TitsMS.M (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (4 * 1 + t), true)) = true := by quickRfl
theorem mS3s2 : allN 4 (fun t => bIf(Nat.blt (4 * 2 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
      (fun s => TitsMS.M (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (4 * 2 + t), true)) = true := by quickRfl
theorem mS3s3 : allN 4 (fun t => bIf(Nat.blt (4 * 3 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
      (fun s => TitsMS.M (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (4 * 3 + t), true)) = true := by quickRfl
theorem mS3s4 : allN 4 (fun t => bIf(Nat.blt (4 * 4 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
      (fun s => TitsMS.M (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (4 * 4 + t), true)) = true := by quickRfl
theorem mS3s5 : allN 4 (fun t => bIf(Nat.blt (4 * 5 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
      (fun s => TitsMS.M (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)
      (4 * 5 + t), true)) = true := by quickRfl
theorem mS3s : allN 23 (segCG 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s)) (recI 15781) (recU 2925 15781) (recV 2925 15781)) = true :=
  allN_segCG_of_segCM <| allN_chunks (B := 4) (C := 6) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mS3s0
    | 1, _ => exact mS3s1
    | 2, _ => exact mS3s2
    | 3, _ => exact mS3s3
    | 4, _ => exact mS3s4
    | 5, _ => exact mS3s5
theorem mS3t : allN 2925 (fun l => Nat.ble (pgW 12 (TitsMS.TP 3) l) 2923) = true := by quickRfl
theorem mS3c : Nat.beq (mergeCnt 2925 12 TitsSS.T 2923 128 (TitsMS.TP 3) (TitsMS.PP 3) (fun s => TitsMS.A (Nat.add 384 s))
    (recI 15781) (recU 2925 15781) (recV 2925 15781)) (timedCnt 2925 2923 (TitsMS.TP 3)) = true := by quickRfl
theorem mS3f : finalC 2925 12 2923 23 (TitsMS.TP 3) (fun s => TitsMS.A (Nat.add 384 s)) = true := by quickRfl
theorem mS3 : mergeCKG 2925 12 2 TitsSS.T 0 107 2923 128 23 (recI 15781) (recU 2925 15781) (recV 2925 15781) (TitsMS.TP 3) (TitsMS.PP 3)
    (fun s => TitsMS.A (Nat.add 384 s)) = true :=
  mergeCKG_of mS3h mS3a mS3s mS3t mS3c mS3f

end CertificateChecks.KernelSporSch.TitsPrim

end
