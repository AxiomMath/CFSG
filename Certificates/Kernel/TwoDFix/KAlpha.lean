module

public import Certificates.Kernel.TwoDFix.Glue

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTwoDFix

open CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix
open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.Co2

theorem alphaK_lifts : liftsK = true := by decide +kernel

theorem alphaK_sR : ((List.range 22).all fun t => sR[t]! == vecW sWord (2 ^ t)) = true := by
  decide +kernel

theorem alphaK_m0 : (List.range' 0 128).all (fun m => m == 0 || m == 16 ||
      (((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) != vecW (subWord coGens m) sR[t]!) &&
       ((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) !=
          Native.actD 22 (liftRows 32) (vecW (subWord coGens m) sR[t]!)))) = true := by
  decide +kernel

theorem alphaK_m1 : (List.range' 128 128).all (fun m => m == 0 || m == 16 ||
      (((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) != vecW (subWord coGens m) sR[t]!) &&
       ((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) !=
          Native.actD 22 (liftRows 32) (vecW (subWord coGens m) sR[t]!)))) = true := by
  decide +kernel

theorem alphaK_m2 : (List.range' 256 128).all (fun m => m == 0 || m == 16 ||
      (((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) != vecW (subWord coGens m) sR[t]!) &&
       ((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) !=
          Native.actD 22 (liftRows 32) (vecW (subWord coGens m) sR[t]!)))) = true := by
  decide +kernel

theorem alphaK_m3 : (List.range' 384 128).all (fun m => m == 0 || m == 16 ||
      (((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) != vecW (subWord coGens m) sR[t]!) &&
       ((List.range 22).any fun t =>
        Native.actD 22 sR (vecW (subWord coGens m) (2 ^ t)) !=
          Native.actD 22 (liftRows 32) (vecW (subWord coGens m) sR[t]!)))) = true := by
  decide +kernel

theorem range512_split : List.range 512 = List.range' 0 128 ++ List.range' 128 128 ++
    List.range' 256 128 ++ List.range' 384 128 := by
  rw [List.range_eq_range', List.range'_append_1, List.range'_append_1, List.range'_append_1]

theorem alphaK_ok : alphaK = true := by
  unfold alphaK
  rw [range512_split, List.all_append, List.all_append, List.all_append, alphaK_lifts, alphaK_sR,
    alphaK_m0, alphaK_m1, alphaK_m2, alphaK_m3]
  rfl

end CertificateChecks.KernelTwoDFix

end
