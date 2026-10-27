module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def fixN (X : Nat) : Nat :=
  foldN 1408 (fun x s => nIf(Nat.beq (pt X x) x, Nat.succ s, s)) 0

@[expose] noncomputable def fixPair (A t m m' : Nat) : Bool :=
  bAnd(Nat.beq (fixN t) m, Nat.beq (fixN (pc t A)) m')

@[expose] noncomputable def fixK : Bool :=
  strictB (WK wordA) fun A => strictB (WK wordZ) fun Z =>
    bAnd(Nat.beq (fixN A) 0, bAnd(fixPair A Z 0 128, bAnd(fixPair A (pc A Z) 128 0,
      bAnd(fixPair A (WK wordB) 0 0, fixPair A (WK wordZ₁) 0 0))))

end CFSG.KD.HN1408.CzInv

end
