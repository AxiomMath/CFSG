module

public import Init

public section

namespace CFSG.KD.MZC

@[expose] noncomputable def g1 (L : List Nat) (i : Nat) : Nat := List.getD L i (nat_lit 0)

@[expose] noncomputable def g2 (L : List (List Nat)) (c i : Nat) : Nat :=
  List.getD (List.getD L c []) i (nat_lit 0)

@[expose] noncomputable def g3 (L : List (List (List Nat))) (c i : Nat) : List Nat :=
  List.getD (List.getD L c []) i []

@[expose] noncomputable def len2 (L : List (List Nat)) (c : Nat) : Nat :=
  List.length (List.getD L c [])

@[expose] noncomputable def hTo (T : Nat → Nat) (HO : List Nat) (c k : Nat) : Nat :=
  T (Nat.add (List.getD HO c (nat_lit 0)) k)

end CFSG.KD.MZC

end
