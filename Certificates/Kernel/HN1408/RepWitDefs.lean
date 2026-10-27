module

public import Certificates.Kernel.HN1408.CzInvDefs

public section

namespace CFSG.KD.HN1408.CzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KD.HN1408.CzT

@[expose] noncomputable def conjW (w : List Nat) (X : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) X
    (fun j _ acc => strictN (WK [j + 1]) fun G => pc (pc G acc) G) w

@[expose] def witT : List Nat := [1, 2, 1, 4, 4, 3, 2]

@[expose] def witW : List (List Nat) :=
  [[1, 3, 4, 3, 5, 0, 1], [6, 4, 2, 5, 0], [0, 5, 0, 2], [5, 6, 2, 5], [0, 6, 2, 5, 4, 2, 3, 2],
    [6, 2, 4, 6, 1], [0, 2, 5, 0]]

@[expose] noncomputable def witK (c t : Nat) (w : List Nat) : Bool :=
  strictB (R c) fun r => strictB (fd r 0) fun q => strictB (fd r 1) fun q' =>
    bAnd(Nat.blt q 1280, bAnd(Nat.blt q' 24, bAnd(Nat.blt 0 t, bAnd(Nat.blt t 5,
      bAnd(w.all (fun j => Nat.blt j 7), Nat.beq (pc (T0 q) (T1 q')) (conjW w (namedP t)))))))

@[expose] noncomputable def repWitK : Bool :=
  allN 7 fun d => witK (Nat.add d 5) (witT.getD d 0) (witW.getD d [])

end CFSG.KD.HN1408.CzInv

end
