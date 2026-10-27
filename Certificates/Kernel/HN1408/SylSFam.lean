module

public import Certificates.Kernel.HN1408.SylS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.BaseMask

@[expose] noncomputable def famCnt (k : Nat) : Nat :=
  [0, 0, 1, 75, 213, 68, 2].getD k 0

@[expose] noncomputable def famOff (k : Nat) : Nat :=
  [0, 0, 0, 4, 604, 4012, 6188, 6316].getD k 0

@[expose] noncomputable def famGOff (k : Nat) : Nat :=
  [0, 0, 0, 2, 227, 1079, 1419, 1431].getD k 0

@[expose] noncomputable def famLayerOK (k : Nat) : Bool :=
  strictB ivMask (fun IM => allN (famCnt k) (fun h =>
    bAnd(memberK 11 (mask 11) 2 0 2048 SylS.T SylS.FM
        (Nat.add (famOff k) (Nat.mul h (Nat.shiftLeft 1 k))) k,
      extK SylS.FM SylS.FG SylS.CM IM (Nat.add (famOff k) (Nat.mul h (Nat.shiftLeft 1 k)))
        (Nat.add (famGOff k) (Nat.mul h k)) k (famOff (Nat.succ k)) (famCnt (Nat.succ k)))))

theorem fam_layer2 : famLayerOK 2 = true := by quickRfl

theorem fam_layer3 : famLayerOK 3 = true := by quickRfl

theorem fam_layer4 : famLayerOK 4 = true := by quickRfl

theorem fam_layer5 : famLayerOK 5 = true := by quickRfl

theorem fam_layer6 : famLayerOK 6 = true := by quickRfl

theorem fam_neg : (!strictB ivMask (fun IM => allN (famCnt 5) (fun h =>
    extK SylS.FM SylS.FG SylS.CM IM (Nat.add (famOff 5) (Nat.mul h 32))
      (Nat.add (famGOff 5) (Nat.mul h 5)) 5 (famOff 6) 0))) = true := by
  quickRfl

end CFSG.KD.HN1408

end
