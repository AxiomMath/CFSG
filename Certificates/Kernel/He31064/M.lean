module

public import Certificates.Kernel.He31064.D
public import Certificates.Kernel.He31064.X

public section

namespace CFSG.KD.He31064

open CFSG.KC.DcTup

@[expose] def pts : List Nat := [2, 0, 0, 1, 3, 4, 2]

@[expose] def B : List Nat := [0, 1, 3, 4, 2]

@[expose] noncomputable def X (j : Nat) : Nat := nth xn (nth ri j)

@[expose] noncomputable def W (j : Nat) : List Nat := nthL reps j

@[expose] noncomputable def H (j : Nat) : Nat := nth hs j

@[expose] noncomputable def cnt (i j : Nat) : Nat :=
  cntT (X i) 6174 C Q2 RW lv (wordInvL ab (W j) pts)

@[expose] noncomputable def nodeOK (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (stepOK 8330 (nth ab (nthD (0, 0) xp i).1) (nth xn (nthD (0, 0) xp i).2) (nth xn i))
    (tabOK ab [(nthD (0, 0) xp i).1] 8330 (nth xn i))
    (Nat.beq (nthD (0, 0) xp i).2 251)

@[expose] noncomputable def nOK (lo len : Nat) : Bool := allR lo len nodeOK

@[expose] noncomputable def hOK (lo len : Nat) : Bool :=
  allR lo len fun j => Nat.beq (cnt j j) (H j)

@[expose] noncomputable def pOK (lo len : Nat) : Bool :=
  allR lo len fun k => Nat.beq (cnt (nthD (0, 0) pairs k).1 (nthD (0, 0) pairs k).2) 0

@[expose] noncomputable def iOK (lo len : Nat) : Bool :=
  allR lo len fun j => Nat.beq (Nat.add (Nat.mul (invK 8330 lb sel (X j)) 8192) (H j)) (nth IV j)

@[expose] noncomputable def massAll : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j ih => Nat.add (Nat.mul 6174 (Nat.div 6174 (H j))) ih) 133

end CFSG.KD.He31064

end
