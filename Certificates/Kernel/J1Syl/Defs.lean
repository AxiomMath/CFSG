module

public import Certificates.Kernel.J1Syl.Words
public import Certificates.Kernel.Sporadic.J1K.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ1Syl

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.Sporadic.J1.Sylow.Native CertificateChecks.KernelSpor.J1K

@[expose] noncomputable def spW (cs : List Char) : List (List Int) :=
  List.rec (motive := fun _ => List (List Int)) [[]]
    (fun a _ ih => Bool.rec (motive := fun _ => List (List Int))
      (List.rec (motive := fun _ => List (List Int)) [[letterOf a]] (fun w ws _ => (letterOf a :: w) :: ws)
        ih)
      ([] :: ih) (a == ',')) cs

@[expose] noncomputable def TWL : List (List Int) := spW TW.chars

@[expose] noncomputable def NWL : List (List Int) := spW NW.chars

@[expose] noncomputable def wp (w : List Int) (x : Nat) : Nat := List.foldr GJ x w

@[expose] noncomputable def xp (w : List Int) (x : Nat) : Nat := wp w (r32 BE (wp (invWord w) x))

@[expose] noncomputable def keyOf (a b : Nat) : Nat := Nat.add (Nat.mul a (nat_lit 1540)) b

@[expose] noncomputable def nodupB (l : List Nat) (s : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun a _ ih s => bAnd(Nat.beq (Nat.land (Nat.shiftRight s a) (nat_lit 1)) (nat_lit 0),
      ih (Nat.lor s (Nat.shiftLeft (nat_lit 1) a)))) l s

@[expose] noncomputable def keys2 (w : List Int) : List Nat :=
  [keyOf (xp w (nat_lit 0)) (xp w (nat_lit 1)),
    keyOf (xp w (xp w (nat_lit 0))) (xp w (xp w (nat_lit 1)))]

@[expose] noncomputable def keysOK : Bool := nodupB (TWL.flatMap keys2) (nat_lit 0)

@[expose] noncomputable def normAt (w : List Int) (e : Nat) : Bool :=
  allN (nat_lit 1540) fun x =>
    Nat.beq (wp w (r32 BE (wp (invWord w) x)))
      (nIf(Nat.beq e (nat_lit 1), r32 BE x, r32 BE (r32 BE x)))

@[expose] noncomputable def normOK (i : Nat) : Bool :=
  bIf(normAt (NWL.getD i []) (nat_lit 1), true, normAt (NWL.getD i []) (nat_lit 2))

@[expose] noncomputable def vKeysOK : Bool :=
  nodupB (NWL.map fun w => keyOf (wp w (nat_lit 0)) (wp w (nat_lit 1))) (nat_lit 0)

@[expose] noncomputable def movesAll (g gi : Nat → Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(notK (memB (keyOf (g (xp w (gi (nat_lit 0)))) (g (xp w (gi (nat_lit 1)))))
      (keys2 w)), ih)) TWL.tail
where
  memB (y : Nat) (l : List Nat) : Bool :=
    List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a y, true, ih)) l
  notK (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def fW : List Int := NWL.getD (nat_lit 17) []

@[expose] noncomputable def slice (L N s : Nat) (p : Nat → Bool) : Bool :=
  allN L fun d => strictB (Nat.add (Nat.mul s L) d) fun i => bIf(Nat.blt i N, p i, true)

@[expose] noncomputable def fOrd (s : Nat) : Bool :=
  slice (nat_lit 154) (nat_lit 1540) s fun x => Nat.beq (wp fW (wp fW (wp fW (wp fW (wp fW x))))) x

@[expose] noncomputable def fNe : Bool :=
  movesAll.notK (bAnd(Nat.beq (wp fW (nat_lit 0)) (nat_lit 0), Nat.beq (wp fW (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def fMov (s : Nat) : Bool :=
  slice (nat_lit 300) (nat_lit 2926) s fun p => bIf(Nat.beq p (nat_lit 0), true,
    movesAll.notK (movesAll.memB (keyOf (wp fW (xp (TWL.getD p []) (wp (invWord fW) (nat_lit 0))))
      (wp fW (xp (TWL.getD p []) (wp (invWord fW) (nat_lit 1))))) (keys2 (TWL.getD p []))))

@[expose] noncomputable def bOK : Bool :=
  movesAll (r32 BE) (fun x => r32 BE (r32 BE x))

@[expose] noncomputable def shapeOK : Bool :=
  TWL.length == 2926 && NWL.length == 60 && TWL.head? == some []

end CertificateChecks.KernelJ1Syl

end
