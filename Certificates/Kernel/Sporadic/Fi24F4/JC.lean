module

public import Certificates.Kernel.Sporadic.Fi24F4.Data
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Data.Kernel.Spor.Fi24F4J
public import CFSG.Sporadic.Fi24I301.Words

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Fi24R2W CFSG.KC.Fi24F4J CFSG.KD.Fi24Net CFSG.Sporadic.Fi24I301

@[expose] def qW : List (List Int × Nat) :=
  [([2, 1, 2, 1], 5), ([2, 1, 2, 1, 1], 4), ([2, 1, 1, 2, 1], 4), ([1, 2, 1, 2, 1], 4),
    ([1, 2, 1, 1, 2], 4), ([1, 1, 2, 1, 2], 4), ([1, 1, 1, 2, 2, 1, 2], 4),
    ([1, 1, 2, 2, 1, 2, 1], 4), ([2, 2, 2, 1, 2, 1], 5), ([2, 1, 1, 1, 2, 2, 1], 4),
    ([2, 2, 1, 2, 1, 2], 5), ([2, 1, 2, 1, 2, 2], 5), ([1, 1, 2, 2, 1, 1, 1], 5)]

@[expose] def gW (i : Nat) : List Int := genWords.getD i []

@[expose] def nW (k : Nat) : List Int := nWords.getD k []

@[expose] def nRow (k i : Nat) : List Nat := (nMats.getD k []).getD i []

@[expose] noncomputable def swc (i : Nat) : Bool := stageOK NW (cw SA SB (gW i)) (nthW J.sw i)

@[expose] noncomputable def sxc (i : Nat) : Bool := stageOK NW (repL (nthW J.sw i) 4) (nthW J.sx i)

@[expose] noncomputable def cubec (i : Nat) : Bool := stageOK NW (repL (nthW J.sx i) 3) []

@[expose] noncomputable def commc (n : Nat) : Bool :=
  stageOK NW (nthW J.sx (Nat.div n 5) ++ nthW J.sx (Nat.mod n 5))
    (nthW J.sx (Nat.mod n 5) ++ nthW J.sx (Nat.div n 5))

@[expose] noncomputable def indc (n : Nat) : Bool :=
  moves NW (prodW J.sx (digits3 n)) (nthV base (nthV J.mv n))

@[expose] noncomputable def fixc : Bool := CFSG.KC.Fi24FixP.fixOK (CFSG.KC.Fi24NetPt.planeL NW) (nthW J.sx 0) 3240

@[expose] noncomputable def snc (k : Nat) : Bool := stageOK NW (cw SA SB (nW k)) (nthW J.sn k)

@[expose] noncomputable def relc (n : Nat) : Bool :=
  stageOK NW (nthW J.sn (Nat.div n 5) ++ (nthW J.sx (Nat.mod n 5) ++
      CFSG.KC.Fi24R2W.invC (nthW J.sn (Nat.div n 5))))
    (prodW J.sx (nRow (Nat.div n 5) (Nat.mod n 5)))

@[expose] noncomputable def sqc (e : Nat) : Bool :=
  stageOK NW (repL (cwQ SA SB (qW.getD e ([], 0)).1) (qW.getD e ([], 0)).2) (nthW J.sq e)

@[expose] noncomputable def qnec : Bool :=
  differ NW (nthW J.sq 0 ++ nthW J.sq J.qe) (nthW J.sq J.qe ++ nthW J.sq 0) (nthV base J.qb)

end CFSG.KD.Fi24F4

end
