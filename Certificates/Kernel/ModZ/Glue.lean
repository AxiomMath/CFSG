module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G2ModZData
public import Certificates.Data.Kernel.ModZCode
public import Certificates.Data.Kernel.Z4Code
import CFSG.Certificates.Kernel.Z4CodeSound
import CFSG.Certificates.Kernel.ModZCodeSound
import Certificates.Kernel.ModZ.Checks

public section

namespace Certificates.Kernel.ModZ

open CFSG.OddStandard.AltStdSmall4.G2 CFSG.KC.ModZCode CFSG.KC.Z4Code CFSG.KC.T10Code

theorem z4CheckE_kernel : z4CheckE () = true :=
  checkE_of ofCode_mulC mulC_lt (fun _ hm _ hn h => ofCode_inj hm hn h) ofCode_zero rfl Z4M.inE
    inE4c (fun x _ => inE_eq x) SQ4 (2 ^ 8) (Nat.eq_of_beq_eq_true ch36407SQ)
    (all_of_chunks ch36407E0 ch36407E1 ch36407E2 ch36407E3 ch36407E4 ch36407E5 ch36407E6
      ch36407E7)

theorem z4CheckC_kernel : z4CheckC () = true := by
  have h1 := checkC_of ofCode_mulC mulC_lt (fun _ hm _ hn h => ofCode_inj hm hn h) ofCode_zero rfl
    Z4M.toCode Z4M.inM Z4M.inA inM4c inA4c (fun x _ => inM_eq x) (fun x _ => inA_eq x) 64 (2 ^ 7) 4
    (by omega) W4a R4c rfl ch36407Ca (lane R4T) (lane G4T) (lane H4T) (all_of_blocks ch36407C2)
  have h2 := checkC_of ofCode_mulC mulC_lt (fun _ hm _ hn h => ofCode_inj hm hn h) ofCode_zero rfl
    Z4M.toCode Z4M.inM Z4M.inA inM4c inA4c (fun x _ => inM_eq x) (fun x _ => inA_eq x) 64 (2 ^ 8) 8
    (by omega) W4b R4c rfl ch36407Cb (lane R4T) (lane G4T) (lane H4T) (all_of_blocks ch36407C2)
  simp only [z4CheckC, Z4M.reps, Z4M.allL, CFSG.KC.Z4Code.tm_eq, Bool.and_eq_true]
  exact ⟨h1, h2⟩

theorem z8CheckC_kernel {u : (ZMod 8)ˣ} {uv : Nat} (hu : ((uv : ℕ) : ZMod 8) = (u : ZMod 8))
    {W : List (Nat × Nat × Nat × Nat)} {RT GT HT : Nat} (hW : R8c = W.map Prod.fst)
    (h1 : allF1 (mulC8 uv) 8192 (2 ^ 8) 8 512 W = true)
    (h2 : allR (fun b => allR (F2 (mulC8 uv) 8192 inM8c inA8c R8c (lane RT) (lane GT) (lane HT))
      (Nat.mul 128 b) 128) 0 64 = true) : z8CheckC u () = true := by
  have h := checkC_of (ofCode8_mulC8 hu) (mulC8_lt uv) (fun _ hm _ hn h => ofCode8_inj hm hn h)
    ofCode8_zero rfl Z8M.toCode Z8M.inM Z8M.inA inM8c inA8c (fun x _ => inM8_eq x)
    (fun x _ => inA8_eq x) 512 (2 ^ 8) 8 (by omega) W R8c hW h1 (lane RT) (lane GT) (lane HT)
    (all_of_blocks h2)
  simp only [z8CheckC, Z8M.reps, Z8M.allL, tm8_eq]
  exact h

theorem z8CheckC_neg_one_kernel : z8CheckC (-1) () = true :=
  z8CheckC_kernel (uv := 7) (W := W8m) (RT := R8mT) (GT := G8mT) (HT := H8mT) (by decide) rfl
    ch36407Mm ch36407M2m

theorem z8CheckC_three_kernel : z8CheckC Z8M.uThree () = true :=
  z8CheckC_kernel (uv := 3) (W := W8t) (RT := R8tT) (GT := G8tT) (HT := H8tT) rfl rfl
    ch36407Mt ch36407M2t

end Certificates.Kernel.ModZ
