module

public import Certificates.Kernel.Sporadic.Fi24F4.Data
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24F4W

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24F4W CFSG.KC.Fi24Kit CFSG.KD.Fi24Net CFSG.KD.Fi24Kit
open CFSG.KD.Fi24Orb (OL)
open CFSG.KC.Enum (allN)

@[expose] def baseL : List Nat := [0, 305530, 5604, 221549, 266275, 186844]

@[expose] noncomputable def tB (i : Nat) : Bool := Nat.beq (nthN W.tf i) (nat_lit 1)

@[expose] noncomputable def eP (i : Nat) : List Nat := (W.E.getD i []).map fun e => nthN e 0

@[expose] noncomputable def cov (i : Nat) : Bool :=
  coverOK NW NT (nthL W.cs i) (tB i) (W.prods.getD i []) (nthN W.q0 i) (eP i)

@[expose] noncomputable def prd (i : Nat) : Bool :=
  andB (Nat.beq (W.prods.getD i []).length (nthL W.Qc i).length)
    (allN (nthL W.Qc i).length (fun j => andB
      (prodOK NW OL NT baseL (nthL (W.prods.getD i []) j) (nthN (nthL W.Qc i) j) (nthN W.q0 i))
      (commQ OL NT (nthN (nthL W.Qc i) j) (nthN W.q0 i))))

@[expose] noncomputable def wit (i : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (witOK OL NT (nthN W.q0 i) (nthN e 0) (nthN e 1) (nthN e 2)) ih)
    (W.E.getD i [])

@[expose] noncomputable def gph (i : Nat) : Bool :=
  graphOK OL NT (nthL W.Q i) (nthL W.par i) (W.th.getD i []) (nthL W.Q i).length

@[expose] noncomputable def fixq (i : Nat) : Bool := qfixOK NW NT (nthL W.cs i) (tB i) (nthL W.Q i)

@[expose] noncomputable def nd (i : Nat) : Bool :=
  andB (Bool.not (Nat.beq (rPt NW NT (nthL W.cs i) (tB i) (nthN W.xd i))
      (clsK OL NT (nthN W.q0 i) (nthN W.xd i))))
    (Bool.not (Nat.beq (rPt NW NT (nthL W.cs i) (tB i) (nthN W.x1 i)) (nthN W.x1 i)))

end CFSG.KD.Fi24F4

end
