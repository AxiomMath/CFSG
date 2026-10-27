module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData
public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408.Tab4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408 CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def xB (g : List Nat) : Nat := pc (WK wordB) (WK (g ++ wordB ++ g.reverse))

@[expose] noncomputable def ne01K (C D : Nat) : Bool :=
  bIf(Nat.beq (pt C 0) (pt D 0), !Nat.beq (pt C 1) (pt D 1), true)

end CFSG.KD.HN1408.Tab4

end
