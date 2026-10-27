module

public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.WordData

public section

namespace CFSG.KD.HN1408.Tab6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408 CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def powK (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idK (fun _ acc => pc X acc) e

@[expose] noncomputable def xK (g : List Nat) : Nat := pc (WK wordAZ) (WK (g ++ wordAZ ++ g.reverse))

@[expose] noncomputable def conjK (w : List Nat) (S T : Nat) : Bool :=
  Nat.beq (pc (pc (WK w) S) (WK w.reverse)) T

@[expose] noncomputable def movesK (X : Nat) : Bool := !Nat.beq (pt X 0) 0

end CFSG.KD.HN1408.Tab6

end
