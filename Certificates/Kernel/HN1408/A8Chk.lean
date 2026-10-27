module

public import Certificates.Kernel.HN1408.A8Data
public import Certificates.Kernel.HN1408.SpecDefs
public import Certificates.Data.Kernel.Spor.MulHF
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

@[expose] noncomputable def a8U : Nat := specK (classb.centGens.map WK) a8SU

@[expose] noncomputable def a8HdO : Bool :=
  bAnd(allN 2 fun j => bAnd(Nat.beq (A8O.G j) (WK (classb.centGens.getD j [])),
      bAnd(canonK 1408 11 (mask 11) (1408 * 11) (A8O.GI j),
        invEqK 1408 11 (mask 11) (1408 * 11) (A8O.G j) (A8O.GI j))),
    bAnd(Nat.beq A8O.cnt 105, bAnd(Nat.beq A8O.R a8U, penumHdK A8O.R A8O.cnt 100000 A8O.T A8O.PL)))

@[expose] noncomputable def a8RecO : Bool :=
  bAnd(penumSlK 1408 11 (mask 11) (1408 * 11) true A8O.G A8O.GI 2 A8O.cnt A8O.T A8O.PL A8O.POS
      A8O.SRT A8O.SRI 0 A8O.cnt,
    slK A8O.cnt (hsortPtKF 1408 11 (mask 11) A8O.cnt A8O.T A8O.HS A8O.HSI) 0 A8O.cnt)

@[expose] noncomputable def a8HdS : Bool :=
  bAnd(allN 5 fun j => bAnd(Nat.beq (A8S.G j) idK,
      bAnd(Nat.beq (A8S.GI j) (specK (classb.centGens.map WK) (a8Row.stab.getD j [])),
        commP (A8S.GI j) A8O.R)),
    bAnd(Nat.beq A8S.cnt 768, penumHdK idK A8S.cnt 100000 A8S.T A8S.PL))

theorem a8kHdO : a8HdO = true := by quickRfl
theorem a8kRecO : a8RecO = true := by quickRfl
theorem a8kHdS : a8HdS = true := by quickRfl

theorem a8kInv :
    bAnd(invEqK 1408 11 (mask 11) (1408 * 11) (specK (classb.centGens.map WK) a8SX)
        (specK ((classb.centGens.map List.reverse).map WK) a8SX.reverse),
      bAnd(invEqK 1408 11 (mask 11) (1408 * 11) (specK (classb.centGens.map WK) a8SY)
        (specK ((classb.centGens.map List.reverse).map WK) a8SY.reverse),
      bAnd(invEqK 1408 11 (mask 11) (1408 * 11) (WK a8WZ) (WK a8WZ.reverse),
        invEqK 1408 11 (mask 11) (1408 * 11) idK idK))) = true := by
  quickRfl

theorem a8kComm :
    Nat.beq (pc (pc (pc (specK (classb.centGens.map WK) a8SX) (specK (classb.centGens.map WK) a8SY))
      (specK ((classb.centGens.map List.reverse).map WK) a8SX.reverse))
      (specK ((classb.centGens.map List.reverse).map WK) a8SY.reverse)) a8U = true := by
  quickRfl

theorem a8kConj : Nat.beq (pc (pc (WK a8WZ) (WK wordZ)) (WK a8WZ.reverse)) a8U = true := by
  quickRfl

end CFSG.KD.HN1408

end
