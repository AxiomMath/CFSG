module

public import Init

public section

namespace CertificateChecks.KernelM23Mult

@[expose] noncomputable def rels6 : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)],
    [(1, true), (1, true)],
    [(2, true), (2, true)],
    [(3, true), (3, true)],
    [(4, true), (4, true)],
    [(5, true), (5, true)],
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true)],
    [(0, true), (2, true), (0, true), (2, true)],
    [(0, true), (3, true), (0, true), (3, true)],
    [(0, true), (4, true), (0, true), (4, true)],
    [(0, true), (5, true), (0, true), (5, true)],
    [(1, true), (2, true), (1, true), (2, true), (1, true), (2, true), (1, true), (2, true),
      (1, true), (2, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(1, true), (4, true), (1, true), (4, true)],
    [(1, true), (5, true), (1, true), (5, true), (1, true), (5, true)],
    [(2, true), (3, true), (2, true), (3, true), (2, true), (3, true)],
    [(2, true), (4, true), (2, true), (4, true), (2, true), (4, true), (2, true), (4, true)],
    [(2, true), (5, true), (2, true), (5, true)],
    [(3, true), (4, true), (3, true), (4, true), (3, true), (4, true)],
    [(3, true), (5, true), (3, true), (5, true), (3, true), (5, true)],
    [(4, true), (5, true), (4, true), (5, true)],
    [(0, true), (2, true), (4, true), (2, true), (4, true)],
    [(1, true), (2, true), (3, true), (1, true), (2, true), (3, true), (1, true), (2, true),
      (3, true), (1, true), (2, true), (3, true), (1, true), (2, true), (3, true)],
    [(1, true), (2, true), (3, true), (5, true), (1, true), (2, true), (3, true), (5, true),
      (1, true), (2, true), (3, true), (5, true), (1, true), (2, true), (3, true), (5, true),
      (1, true), (2, true), (3, true), (5, true)]]

@[expose] noncomputable def coverW : List (List (Nat × Bool)) :=
  [[(0, false), (2, true), (4, true), (2, false), (4, false)],
    [(1, false), (0, true), (1, true), (0, false), (1, false), (2, true), (4, true), (2, false),
      (4, false)],
    [(2, false), (1, true), (0, true), (1, false), (0, false), (4, true), (2, true), (1, true),
      (2, true), (1, true), (2, false), (1, false), (2, false), (4, false), (1, false)],
    [(3, false), (1, true), (2, true), (1, false), (2, false), (1, true), (3, true), (2, true),
      (1, true), (2, true), (3, false), (1, false), (2, false), (1, false), (2, false)],
    [(4, false), (2, true), (1, true), (2, false), (1, false), (3, true), (2, true), (1, true),
      (2, true), (1, true), (0, true), (3, true), (4, true), (2, false), (1, false), (2, false),
      (3, false), (4, false), (3, false), (0, false), (1, false)],
    [(5, false), (1, true), (5, true), (1, false), (5, false), (4, true), (0, true), (1, true),
      (2, true), (4, false), (2, false), (1, false), (0, false)]]

@[expose] noncomputable def appendK {α : Type} (a b : List α) : List α :=
  List.rec (motive := fun _ => List α) b (fun x _ ih => x :: ih) a

@[expose] noncomputable def invK (w : List (Nat × Bool)) : List (Nat × Bool) :=
  List.rec (motive := fun _ => List (Nat × Bool) → List (Nat × Bool)) (fun acc => acc)
    (fun l _ ih acc => ih (Prod.rec (motive := fun _ => Nat × Bool)
      (fun g b => (g, Bool.rec true false b)) l :: acc)) w []

@[expose] noncomputable def commK (i : Nat) (r : List (Nat × Bool)) : List (Nat × Bool) :=
  (i, true) :: appendK r ((i, false) :: invK r)

@[expose] noncomputable def coverK (gs : List Nat) (R cw : List (List (Nat × Bool))) :
    List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) cw
    (fun i _ ih => List.rec (motive := fun _ => List (List (Nat × Bool))) ih
      (fun r _ ih' => commK i r :: ih') R) gs

@[expose] noncomputable def allLtK (m : Nat) (w : List (Nat × Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => Bool.rec false ih (Prod.rec (motive := fun _ => Bool) (fun g _ => Nat.blt g m) l))
    w

@[expose] noncomputable def filterK (m : Nat) (ws : List (List (Nat × Bool))) : List (List (Nat × Bool)) :=
  List.rec (motive := fun _ => List (List (Nat × Bool))) []
    (fun w _ ih => Bool.rec ih (w :: ih) (allLtK m w)) ws

@[expose] noncomputable def rels5 : List (List (Nat × Bool)) := filterK 5 rels6

@[expose] noncomputable def cover6 : List (List (Nat × Bool)) := coverK [0, 1, 2, 3, 4, 5] rels6 coverW

@[expose] noncomputable def cover5 : List (List (Nat × Bool)) := filterK 5 cover6

end CertificateChecks.KernelM23Mult

end
