module

public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5BridgeCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace CFSG.KD.HN1408

open CFSG.EvenSporadicStandard.HNRecog.Simple2S5

@[expose] noncomputable def brW (X : Nat) (s : List Nat) : Bool :=
  Nat.beq (pt X 0) 0 &&
    (List.range 50).all fun l => Nat.beq (pt X bridgePts[l]!) bridgePts[s[l]!]!

@[expose] noncomputable def brK : Bool :=
  (List.range 6).all fun k => brW (WK bridgeWords[k]!) HNUnitaryBridge.smallPermLists[k]!

theorem brK_true : brK = true := by quickRfl

end CFSG.KD.HN1408

end
