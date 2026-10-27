module

public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24Oct

public section

namespace CFSG.KD.Fi24Oct

open CFSG.KC CFSG.KC.Fi24Oct CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def nthO {α : Type} (d : α) (l : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ ih j => Nat.rec (motive := fun _ => α) a (fun k _ => ih k) j) l i

@[expose] noncomputable def pts : List Nat := [
  0, 235226, 260113, 28578, 188745, 203738, 125431, 94037, 226468, 170631, 98324, 93939, 183511,
  152544, 270869, 165737, 248839, 125087, 293, 148787, 28756, 264917, 118401, 212333]

@[expose] noncomputable def wcs : List (List Nat) := [
  [], [24, 23, 14, 5, 0], [19, 9, 7, 8, 0], [22, 14, 13, 5, 0], [25, 12, 25, 0], [12, 3, 16, 3, 0],
  [8, 7, 18, 5, 0], [9, 23, 6, 11, 0], [5, 13, 24, 7, 0], [13, 6, 15, 4, 0], [20, 23, 19, 6, 0],
  [8, 20, 6, 11, 0], [14, 16, 22, 0], [8, 6, 8, 0], [0, 15, 21, 6, 0], [3, 21, 10, 7, 2],
  [20, 9, 6, 0], [2, 0, 10, 7, 2], [22, 12, 15, 8, 4, 0], [11, 7, 18, 6, 0], [8, 24, 6, 4, 0],
  [18, 15, 7, 24, 0], [18, 10, 9, 5, 0], [23, 21, 4, 0]]

@[expose] noncomputable def wc (i : Nat) : List Nat := nthO [] wcs i

@[expose] noncomputable def nc (k : Nat) : List Nat := nthO [] [
  [17, 6, 20, 6, 6, 4, 15, 16, 24, 15, 8, 19, 15, 23, 19, 15, 22, 19, 17, 25],
  [22, 12, 15, 8, 4, 0, 19, 14, 10, 16, 5, 11, 19, 9, 25, 20, 8, 12, 14, 21, 13, 14, 12, 18, 16, 21,
    26]] k

@[expose] noncomputable def perm (k : Nat) : List Nat := nthO [] [
  [0, 23, 2, 3, 9, 22, 11, 12, 17, 4, 19, 6, 7, 13, 14, 15, 16, 8, 20, 10, 18, 21, 5, 1],
  [18, 22, 20, 8, 15, 2, 13, 17, 14, 12, 23, 21, 16, 19, 0, 7, 11, 5, 1, 6, 10, 3, 4, 9]] k

@[expose] noncomputable def o0 : List Nat := [0, 2, 3, 13, 14, 15, 16, 21]

@[expose] noncomputable def sep : Nat := 59207

@[expose] noncomputable def we : List (List Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat × Nat)) (fun _ => List.nil)
    (fun p _ ih i => (wc i, p) :: ih (Nat.succ i)) pts (nat_lit 0)

@[expose] noncomputable def pq (k : Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun p _ ih i => (p, nthO 0 pts (nthO 0 (perm k) i)) :: ih (Nat.succ i)) pts (nat_lit 0)

@[expose] noncomputable def ow : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil (fun i _ ih => wc i :: ih) o0

@[expose] noncomputable def rt : Bool := rootOK NW NT we

@[expose] noncomputable def cm : Bool := commOK NW NT we

@[expose] noncomputable def pr : Bool := pairsOK NW NT sep we

@[expose] noncomputable def nm (k : Nat) : Bool := normOK NW NT (nc k) (pq k)

@[expose] noncomputable def pd : Bool := prodOK NW NT ow

end CFSG.KD.Fi24Oct

end
