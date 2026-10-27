module

public import Certificates.Kernel.HN1408.CzTDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def gensCommK (ws : List (List Nat)) (Zw : List Nat) : Bool :=
  strictB (WK Zw) fun Z => allN 2 fun l => commP (WK (ws.getD l [])) Z

theorem cbComm_ok : gensCommK classb.centGens wordB = true := by quickRfl

theorem cazComm_ok : gensCommK classaz.centGens wordZ = true := by quickRfl

theorem cbComm_neg : (!gensCommK classb.centGens wordZ) = true := by quickRfl

theorem cazComm_neg : (!gensCommK classaz.centGens wordB) = true := by quickRfl

end CFSG.KD.HN1408.CzInv

end
