module

public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24ThreeAK

public section

namespace CFSG.KD.Fi24ThreeAK

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeAK CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def ev : List Nat := [8, 10, 12, 14, 16, 18, 20, 22, 24]

@[expose] noncomputable def S0 : Nat := nat_lit 8238

@[expose] noncomputable def F3 : Nat :=
  Nat.lor (nat_lit 1) (Nat.lor (Nat.shiftLeft (nat_lit 1) (nat_lit 73618))
    (Nat.shiftLeft (nat_lit 1) (nat_lit 305530)))

@[expose] noncomputable def reps : List Nat := [1, 2, 3, 5, 13]

@[expose] noncomputable def tests : List Nat := [0, 5604, 305530, 0, 0]

@[expose] noncomputable def base : List Nat := [0, 305530, 5604, 221549, 266275, 186844]

@[expose] noncomputable def words : List (List Nat) := [
  [25, 17, 25, 12, 15, 13, 16, 15, 10, 12, 12, 20],
  [24, 17, 24, 18, 14, 14, 21, 25, 13, 23, 8, 18, 14, 24, 18, 11],
  [25, 18, 22, 21, 14, 13, 23, 17, 20, 11, 24, 13, 22, 17],
  [19, 14, 20, 13, 17, 10, 17, 19, 21],
  [25, 16, 21, 16, 23, 14, 14, 14, 24, 15, 12, 12, 11, 12, 9, 24, 10],
  [25, 17, 25, 13, 18, 14, 14, 14, 11, 11, 22, 14, 13],
  [25, 18, 21, 17, 14, 12, 14, 21, 16, 15, 8, 13, 20, 8, 10],
  [16, 23, 18, 14, 14, 13, 23, 14, 24, 8, 12, 19, 21, 11, 13]]

@[expose] noncomputable def W (i : Nat) : List Nat := nthL words i

@[expose] noncomputable def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true), (0, true)], [(1, true), (1, true), (1, true)],
  [(4, true), (4, true), (4, true)], [(5, true), (5, true), (5, true)],
  [(2, true), (2, true), (2, true)], [(3, true), (3, true), (3, true)],
  [(0, false), (4, false), (0, true), (4, true), (2, false)],
  [(0, false), (5, false), (0, true), (5, true)],
  [(0, false), (2, false), (0, true), (2, true)],
  [(0, false), (3, false), (0, true), (3, true), (5, false), (5, false)],
  [(1, false), (4, false), (1, true), (4, true)],
  [(1, false), (5, false), (1, true), (5, true), (3, false), (3, false)],
  [(1, false), (2, false), (1, true), (2, true), (4, false)],
  [(1, false), (3, false), (1, true), (3, true)],
  [(4, false), (2, false), (4, true), (2, true)],
  [(4, false), (3, false), (4, true), (3, true), (1, false)],
  [(5, false), (2, false), (5, true), (2, true), (0, false), (0, false)],
  [(5, false), (3, false), (5, true), (3, true)],
  [(0, true), (1, false), (0, true), (1, true), (0, false), (1, true)],
  [(4, true), (5, false), (4, true), (5, true), (4, false), (5, true)],
  [(2, true), (3, false), (2, true), (3, true), (2, false), (3, true)]]

@[expose] noncomputable def cW : List Nat := [5, 6, 14, 11, 19, 1, 4, 22, 11, 6]

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih j => Nat.rec (motive := fun _ => Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def cov : Bool := coverOK NW ev (nat_lit 8) S0 F3

@[expose] noncomputable def fl (i : Nat) : Bool := failOK CFSG.KD.Fi24Orb.OL NT (nthN reps i) (nthN tests i)

@[expose] noncomputable def line : Bool :=
  Nat.beq (clsK CFSG.KD.Fi24Orb.OL NT (nat_lit 0) (nat_lit 305530)) (nat_lit 73618)

@[expose] noncomputable def d4 (b : Nat) : Bool := d4At NW W rels (nthN base b)

@[expose] noncomputable def mv : Bool :=
  andB (notB (Nat.beq (wP NW (W 0) (nat_lit 5604)) (nat_lit 5604)))
    (notB (Nat.beq (wP NW (W 2) (nat_lit 5604)) (nat_lit 5604)))

@[expose] noncomputable def fix : Bool :=
  allL (fun i => andB (Nat.beq (wP NW (W i) (nat_lit 0)) (nat_lit 0))
    (Nat.beq (wP NW (W i) (nat_lit 305530)) (nat_lit 305530))) [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] noncomputable def cj (b : Nat) : Bool :=
  conjOK NW CFSG.KD.Fi24Orb.OL NT cW (nthN base b)

end CFSG.KD.Fi24ThreeAK

end
