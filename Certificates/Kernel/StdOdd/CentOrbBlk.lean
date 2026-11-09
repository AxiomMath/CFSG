module

public import Certificates.Kernel.StdOdd.CentPopH

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KC.Misc.E6Std

@[expose] noncomputable def orbPlane (X : Nat) (U : List Nat) (m p c : Nat) : Nat :=
  forceN (full m) fun F =>
  Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k ih => Nat.lor ih (Nat.shiftLeft
      (Nat.land (rowX (Nat.shiftRight (powB X k) (Nat.mul (nat_lit 156) c)) U) F) (Nat.mul k m))) p)
    (Nat.shiftLeft (Nat.shiftRight (nthN U c) m) (Nat.mul p m))

@[expose] noncomputable def orbNetOK (Ds Ms PL : List Nat) (X : Nat) (U : List Nat) (m p g s : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => andB (forceB (Nat.add (Nat.mul g s) j) fun c =>
      Nat.beq (net Ds Ms (nthN PL c)) (orbPlane X U m p c)) ih) g

namespace CentData

variable (D : CentData)

@[expose] noncomputable def orbChunkB (d : ℕ) (U : List ℕ) (A B m : ℕ) (cs : List ℕ) (q : ℕ) : Bool :=
  forceB (Nat.min 262144 (Nat.sub m (Nat.mul q 262144))) fun w =>
  popHB d (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd)
    (chunkPl U (Nat.mul q 262144) w) w Form.fmPk Form.brPk) (nthN cs q)

@[expose] noncomputable def orbFixB (U : List ℕ) (A B m f : ℕ) : Bool :=
  Nat.beq (profAll (D.xB A B) (D.K1.map Prod.fst) (D.K1.map Prod.snd) (chunkPl U m f) f Form.fmPk
    Form.brPk) 0

end CentData

end CFSG.KD.StdOdd.Cent

end
