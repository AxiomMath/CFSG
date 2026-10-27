module

public import Certificates.Kernel.HN1408.M11Data
public import Certificates.Kernel.HN1408.Words

public section

namespace CFSG.KD.HN1408.AK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408

@[expose] noncomputable def commAt (R Y p : Nat) : Bool := Nat.beq (pt R (pt Y p)) (pt Y (pt R p))

@[expose] noncomputable def commF (R Y : Nat) : Bool :=
  bIf(commAt R Y 0, bIf(commAt R Y 1, bIf(commAt R Y 2, bIf(commAt R Y 3, commP R Y, false),
    false), false), false)

@[expose] noncomputable def cntR (Y s : Nat) : Nat :=
  foldN 525 (fun i s => nIf(commF (MRZ i) Y, Nat.succ s, s)) s

@[expose] noncomputable def cntZ (X : Nat) : Nat :=
  foldN 11 (fun k s => strictN (pc (MYP (11 - k)) (pc X (MYP k))) fun Y => cntR Y s) 0

@[expose] noncomputable def cntK : Bool :=
  bAnd(Nat.beq (cntZ (WK wordB)) 315, Nat.beq (cntZ (WK wordZ₁)) 75)

end CFSG.KD.HN1408.AK

end
