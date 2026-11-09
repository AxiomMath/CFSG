module

public import Certificates.Kernel.Sporadic.Fi24F3d.M1
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Fi24F3d

@[expose] def WD2 : List Nat := [11, 10, 0, 1, 4, 3, 5, 4, 6, 5]

@[expose] def MN2 : List (Nat × Nat) :=
  [(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 8), (1, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5),
    (1, 6), (1, 7), (2, 8), (2, 10), (0, 12), (1, 9), (2, 7), (2, 9), (0, 11), (1, 0), (1, 1),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9), (0, 10), (1, 0), (1, 1), (1, 2),
    (1, 3)]

@[expose] def MF2 : List (Nat × Nat) :=
  [(1, 7), (1, 8), (1, 6), (2, 4), (2, 6), (2, 8), (0, 10)]

@[expose] def WD3 : List Nat := [11, 10, 0, 1, 5, 4, 3, 6, 5, 4]

@[expose] def MN3 : List (Nat × Nat) :=
  [(1, 11), (0, 12), (2, 9), (0, 11), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6),
    (1, 7), (1, 8), (1, 9), (0, 10), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 1), (1, 2),
    (1, 3), (1, 4), (1, 0), (1, 1), (1, 2), (1, 3)]

@[expose] def MF3 : List (Nat × Nat) :=
  [(1, 7), (1, 8), (1, 6), (2, 4), (2, 6), (2, 8), (0, 10), (1, 9), (1, 7), (1, 5), (1, 6), (2, 7),
    (2, 9), (0, 11), (1, 6), (1, 7), (2, 4), (1, 6), (2, 7), (1, 9), (0, 10)]

@[expose] def WD4 : List Nat := [11, 10, 0, 1, 6, 5, 4, 3]

@[expose] def MN4 : List (Nat × Nat) :=
  [(1, 3), (1, 4), (1, 5), (1, 6), (0, 7), (2, 0), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 7),
    (1, 9), (0, 10), (1, 8), (0, 9), (1, 7), (0, 8), (1, 1), (1, 2), (1, 3), (1, 4), (1, 0), (1, 1),
    (1, 2), (1, 3)]

@[expose] def MF4 : List (Nat × Nat) :=
  [(1, 7), (1, 8), (1, 6), (2, 4), (2, 6), (2, 8), (0, 10), (1, 9), (1, 7), (1, 5), (1, 6), (2, 7),
    (2, 9), (0, 11), (1, 6), (1, 7), (2, 4), (1, 6), (2, 7), (1, 9), (0, 10), (1, 6), (1, 7), (2, 8),
    (0, 10), (1, 5), (2, 6), (1, 8), (0, 9), (2, 4), (1, 6), (1, 7), (0, 8)]

theorem M2.n2u : cxOK MN2 (N2.reverse ++ WEF ++ N2) WD2 = true := by quickRfl

theorem M2.n2v : cxOK MF2 (WE ++ WF ++ WF) WD2 = true := by quickRfl

theorem M2.n3u : cxOK MN3 (N3.reverse ++ WEF ++ N3) WD3 = true := by quickRfl

theorem M2.n3v : cxOK MF3 (WE ++ WF ++ WF ++ WF) WD3 = true := by quickRfl

theorem M2.n4u : cxOK MN4 (N4.reverse ++ WEF ++ N4) WD4 = true := by quickRfl

theorem M2.n4v : cxOK MF4 (WE ++ WF ++ WF ++ WF ++ WF) WD4 = true := by quickRfl

theorem M2.n2 {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((N2.reverse ++ WEF ++ N2).map s).prod = ((WE ++ WF ++ WF).map s).prod :=
  (prod_of_cxOK hs M2.n2u).trans (prod_of_cxOK hs M2.n2v).symm

theorem M2.n3 {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((N3.reverse ++ WEF ++ N3).map s).prod = ((WE ++ WF ++ WF ++ WF).map s).prod :=
  (prod_of_cxOK hs M2.n3u).trans (prod_of_cxOK hs M2.n3v).symm

theorem M2.n4 {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((N4.reverse ++ WEF ++ N4).map s).prod = ((WE ++ WF ++ WF ++ WF ++ WF).map s).prod :=
  (prod_of_cxOK hs M2.n4u).trans (prod_of_cxOK hs M2.n4v).symm

end CFSG.KD.Fi24F3d

end
