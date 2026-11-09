module

public import Certificates.Kernel.SporSch.Tits.Prim2269K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KC.MergeG
open CertificateChecks.KernelSporSch

theorem mS2h : bAnd(Nat.blt 0 2925, bAnd(Nat.blt 27 2925, bAnd(Nat.blt 2923 4096, bAnd(Nat.blt 0 128,
    Nat.ble 2923 (Nat.mul 128 23))))) = true := by quickRfl
theorem mS2a : allN 2925 (fun y => Nat.beq (pgW 12 (TitsMS.A 256) y)
    (nIf(Nat.beq y 27, 0, y))) = true := by quickRfl
theorem mS2s0 : allN 4 (fun t => bIf(Nat.blt (4 * 0 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
      (fun s => TitsMS.M (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)
      (4 * 0 + t), true)) = true := by quickRfl
theorem mS2s1 : allN 4 (fun t => bIf(Nat.blt (4 * 1 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
      (fun s => TitsMS.M (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)
      (4 * 1 + t), true)) = true := by quickRfl
theorem mS2s2 : allN 4 (fun t => bIf(Nat.blt (4 * 2 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
      (fun s => TitsMS.M (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)
      (4 * 2 + t), true)) = true := by quickRfl
theorem mS2s3 : allN 4 (fun t => bIf(Nat.blt (4 * 3 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
      (fun s => TitsMS.M (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)
      (4 * 3 + t), true)) = true := by quickRfl
theorem mS2s4 : allN 4 (fun t => bIf(Nat.blt (4 * 4 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
      (fun s => TitsMS.M (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)
      (4 * 4 + t), true)) = true := by quickRfl
theorem mS2s5 : allN 4 (fun t => bIf(Nat.blt (4 * 5 + t) 23,
    segCM 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
      (fun s => TitsMS.M (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)
      (4 * 5 + t), true)) = true := by quickRfl
theorem mS2s : allN 23 (segCG 2925 12 2 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s)) (recI 12858) (recU 2925 12858) (recV 2925 12858)) = true :=
  allN_segCG_of_segCM <| allN_chunks (B := 4) (C := 6) (by norm_num) fun c hc => by
    match c, hc with
    | 0, _ => exact mS2s0
    | 1, _ => exact mS2s1
    | 2, _ => exact mS2s2
    | 3, _ => exact mS2s3
    | 4, _ => exact mS2s4
    | 5, _ => exact mS2s5
theorem mS2t : allN 2925 (fun l => Nat.ble (pgW 12 (TitsMS.TP 2) l) 2923) = true := by quickRfl
theorem mS2c : Nat.beq (mergeCnt 2925 12 TitsSS.T 2923 128 (TitsMS.TP 2) (TitsMS.PP 2) (fun s => TitsMS.A (Nat.add 256 s))
    (recI 12858) (recU 2925 12858) (recV 2925 12858)) (timedCnt 2925 2923 (TitsMS.TP 2)) = true := by quickRfl
theorem mS2f : finalC 2925 12 2923 23 (TitsMS.TP 2) (fun s => TitsMS.A (Nat.add 256 s)) = true := by quickRfl
theorem mS2 : mergeCKG 2925 12 2 TitsSS.T 0 27 2923 128 23 (recI 12858) (recU 2925 12858) (recV 2925 12858) (TitsMS.TP 2) (TitsMS.PP 2)
    (fun s => TitsMS.A (Nat.add 256 s)) = true :=
  mergeCKG_of mS2h mS2a mS2s mS2t mS2c mS2f

end CertificateChecks.KernelSporSch.TitsPrim

end
