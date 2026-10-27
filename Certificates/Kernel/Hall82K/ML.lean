module

public import Certificates.Kernel.Hall82K.MLData
public import Certificates.Kernel.Hall82K.DAData
public import Certificates.Kernel.Hall82K.EnumData
public import Certificates.Data.Kernel.Hall82K.Bridge
public import CFSG.CGT.Hall82.ModelData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Hall82L

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.Hall82K CFSG.KD.Hall82E CFSG.KD.Hall82A CFSG.CGT.Hall82

theorem ch840001root : rootK EM MRT 52077576321 61871938592 = true := by decide +kernel

theorem ch840001zeta : andB (Nat.blt MZI 1080) (Nat.beq (EL MZI) DZC) = true := by decide +kernel

theorem ch840001comm :
    commK 52077576321 DZC = true ∧ commK 61871938592 DZC = true ∧
      commK 4439643498 DZC = false := by
  decide +kernel

theorem ch840001center : P.allN 1080 (centerAtK EL DZC MCW) = true := by decide +kernel

theorem ch840001nv : P.allN 2160 (nvAtZK EM EL MNV) = true := by decide +kernel

theorem ch840001conjT : P.allN 1080 (conjTAtK EL TC MCT) = true := by decide +kernel

theorem ch840001fix8 : P.allN 2160 (fix8AtK EM DZC MF8) = true := by decide +kernel

theorem ch840001yt :
    permK YC = true ∧ permK TC = true ∧ zipArrK [YC, TC] [hallY, hallT] = true ∧
      andB (Nat.blt (lane MYI 11 2047 0) 1080) (Nat.beq (EL (lane MYI 11 2047 0)) YC) = true ∧
      andB (Nat.blt (lane MYI 11 2047 1) 1080) (Nat.beq (EL (lane MYI 11 2047 1)) TC) = true ∧
      compL TC TC = idK ∧ powL YC 4 = idK ∧ negK (Nat.beq (powL YC 2) idK) = true ∧
      compL (compL TC YC) (compL TC YC) = idK := by
  decide +kernel

theorem ch840001ytEnum : P.allN 8 (enumAt YC TC 8 EY PY SY CY) = true := by decide +kernel

end CFSG.KD.Hall82L
