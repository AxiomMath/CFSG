module

public import Certificates.Kernel.IdxFour.TcosetData
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.GF2Type.Smith1979.IdxFourModelData
public import CFSG.GF2Type.Smith1979.IdxFourModelDefs

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4T

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4T CFSG.GF2Type.Smith1979.IdxFour

@[expose] noncomputable def cf17610rec (k : Nat) : Bool :=
  recOK (lbarGens.map packR) (packL vtBasis) (nthD [] TR k) (nthD [] TW k)

theorem cf17610mask :
    maskOK (lbarGens.map packR) (packR omegaRows) (TR.map fun r => nthD 0 r 0) = true := by
  decide +kernel

#kc_each cf17610rec 0 15

theorem cf17610len : lenN TR = 15 ∧ lenN TW = 15 := by decide +kernel

theorem cf17610neg_mask :
    maskOK (lbarGens.map packR) (packR omegaRows) ((TR.map fun r => nthD 0 r 0).tail) = false := by
  decide +kernel

@[expose] noncomputable def setR (i v : Nat) : List Nat := (nthD [] TR 0).set i v

theorem cf17610neg_e :
    recOK (lbarGens.map packR) (packL vtBasis) (setR 2 (Nat.xor (nthD 0 (nthD [] TR 0) 2) 1))
      (nthD [] TW 0) = false := by
  decide +kernel

theorem cf17610neg_f :
    recOK (lbarGens.map packR) (packL vtBasis)
      (setR 5 (Nat.xor (nthD 0 (nthD [] TR 0) 5) (2 ^ 4))) (nthD [] TW 0) = false := by
  decide +kernel

theorem cf17610neg_am :
    recOK (lbarGens.map packR) (packL vtBasis) (setR 6 (Nat.xor (nthD 0 (nthD [] TR 0) 6) 2))
      (nthD [] TW 0) = false := by
  decide +kernel

theorem cf17610neg_len :
    recOK (lbarGens.map packR) (packL vtBasis) (nthD [] TR 0) (nthD [] TW 0).tail = false := by
  decide +kernel

theorem cf17610neg_wit :
    recOK (lbarGens.map packR) (packL vtBasis) (nthD [] TR 0)
      ((nthD [] TW 0).set 255 (nthD 0 (nthD [] TW 0) 255 + 3)) = false := by
  decide +kernel

end CFSG.KD.IF4T

end
