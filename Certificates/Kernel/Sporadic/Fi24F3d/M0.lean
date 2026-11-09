module

public import Certificates.Kernel.Sporadic.Fi24F3d.M1
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Fi24F3d

@[expose] def ME5 : List (Nat × Nat) :=
  [(1, 3), (1, 4), (1, 2), (2, 0), (2, 2), (2, 4), (0, 6), (1, 5), (1, 3), (1, 1), (1, 2), (2, 3),
    (2, 5), (0, 7), (1, 2), (1, 3), (2, 0), (1, 2), (2, 3), (1, 5), (0, 6), (1, 2), (1, 3), (2, 4),
    (0, 6), (1, 1), (2, 2), (1, 4), (0, 5), (2, 0), (1, 2), (1, 3), (0, 4), (0, 3), (0, 2), (0, 1),
    (0, 0)]

@[expose] def WDEF : List Nat := [11, 10, 0, 1, 3, 4, 5, 6]

@[expose] def MFE : List (Nat × Nat) :=
  [(1, 3), (1, 4), (1, 5), (1, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 1), (1, 2), (1, 3), (1, 4),
    (1, 0), (1, 1), (1, 2), (1, 3)]

@[expose] def WDEY : List Nat := [11, 10, 0, 1, 8, 7, 3, 4, 5, 6]

@[expose] def MYE : List (Nat × Nat) :=
  [(1, 5), (1, 6), (1, 7), (1, 8), (1, 4), (1, 5), (1, 6), (1, 7), (1, 3), (1, 4), (1, 5), (1, 6),
    (1, 2), (1, 3), (1, 4), (1, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 0), (1, 1), (1, 2), (1, 3)]

theorem M0.e5c : cxOK ME5 (WE ++ WE ++ WE ++ WE ++ WE) [] = true := by quickRfl

theorem M0.efu : cxOK [] (WE ++ WF) WDEF = true := by quickRfl

theorem M0.efv : cxOK MFE (WF ++ WE) WDEF = true := by quickRfl

theorem M0.eyu : cxOK [] (WE ++ WY) WDEY = true := by quickRfl

theorem M0.eyv : cxOK MYE (WY ++ WE) WDEY = true := by quickRfl

theorem M0.e5 {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((WE ++ WE ++ WE ++ WE ++ WE).map s).prod = 1 :=
  (prod_of_cxOK hs M0.e5c).trans (by simp)

theorem M0.ef {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((WE ++ WF).map s).prod = ((WF ++ WE).map s).prod :=
  (prod_of_cxOK hs M0.efu).trans (prod_of_cxOK hs M0.efv).symm

theorem M0.ey {G : Type*} [Group G] {s : Nat → G} (hs : CoxRel s) :
    ((WE ++ WY).map s).prod = ((WY ++ WE).map s).prod :=
  (prod_of_cxOK hs M0.eyu).trans (prod_of_cxOK hs M0.eyv).symm

end CFSG.KD.Fi24F3d

end
