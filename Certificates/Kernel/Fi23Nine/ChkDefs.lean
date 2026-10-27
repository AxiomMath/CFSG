module

public import Certificates.Data.Kernel.Fi23Nine.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23S.Tabs
public import Certificates.Kernel.Fi23Nine.Data
public import CFSG.Sporadic.Fi23.IndexNineInputs

public section

namespace CFSG.KD.Fi23Nine

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Nine CFSG.KD.Fi23K CFSG.KD.Fi23S CFSG.Sporadic.Fi23

@[expose] noncomputable def regZ (z : Int) : Nat := Nat.add (nat_lit 52) (Int.toNat z)

@[expose] noncomputable def cR : List Nat := List.map regZ nineCWord
@[expose] noncomputable def xR : List Nat := List.map regZ nineXWord
@[expose] noncomputable def yR : List Nat := List.map regZ nineYWord
@[expose] noncomputable def hR (j : Nat) : List Nat := List.map regZ (nineHWords.toList.getD j [])

@[expose] def sp : List Nat := 0 :: 1 :: nineE :: nineO4

@[expose] noncomputable def spD (i : Nat) : Nat := fD D (nat_lit 1051) i

@[expose] noncomputable def forF (s : Nat) : Bool :=
  forSl H D (Nat.mul s (nat_lit 4096)) (nat_lit 4096)

@[expose] noncomputable def lgF : Bool := lgK D

@[expose] noncomputable def spF : Bool :=
  bAnd(cK G D cR sp,
  bAnd(Nat.beq (spD (nat_lit 0)) (spD (nat_lit 21)),
  bAnd(Nat.beq (spD (nat_lit 1)) (spD (nat_lit 22)),
  bAnd(Nat.beq (spD (nat_lit 2)) (spD (nat_lit 24)),
  bAnd(Nat.beq (rootOf (fD D (nat_lit 0) (spD (nat_lit 23)))) (nat_lit 1),
  bAnd(allN (nat_lit 4) (fun j =>
      Nat.beq (rootOf (fD D (nat_lit 0) (spD (Nat.add (nat_lit 24) j)))) (nat_lit 2)),
  bAnd(clK H [spD (nat_lit 21)],
  bAnd(clK H [spD (nat_lit 22), spD (nat_lit 23)],
    clK H [spD (nat_lit 24), spD (nat_lit 25), spD (nat_lit 26), spD (nat_lit 27)]))))))))

@[expose] noncomputable def okE (z : Nat) : Bool :=
  bAnd(Nat.blt z (nat_lit 24), bAnd(Nat.beq (tb G (Nat.add (nat_lit 52) z) (nat_lit 0)) (nat_lit 0),
    Nat.beq (tb G (Nat.add (nat_lit 52) z) (nat_lit 1)) (nat_lit 1)))

@[expose] noncomputable def eF : Bool :=
  bAnd(trK (fun z x => tb G (Nat.add (nat_lit 52) z) x) okE D (nat_lit 995) nineE (nat_lit 693),
    srtK D (nat_lit 995) (nat_lit 1017) (nat_lit 693))

@[expose] noncomputable def fF : Bool :=
  bAnd(allN (nat_lit 3) (fun j => bAnd(Nat.beq (wv G (hR j) (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.beq (wv G (hR j) (nat_lit 1)) (nat_lit 1), Nat.beq (wv G (hR j) nineE) nineE))),
  bAnd(trK (fun j x => wv G (hR j) x) (fun j => Nat.blt j (nat_lit 3)) D (nat_lit 1039) nineF
      (nat_lit 180),
    srtK D (nat_lit 1039) (nat_lit 1045) (nat_lit 180)))

@[expose] noncomputable def wlF : Bool :=
  bAnd(ltL (nat_lit 76) cR, bAnd(ltL (nat_lit 76) xR, bAnd(ltL (nat_lit 76) yR,
    allN (nat_lit 3) fun j => ltL (nat_lit 76) (hR j))))

@[expose] noncomputable def xyF : Bool := xyK G xR.reverse yR.reverse [1, nineE] nineO4

end CFSG.KD.Fi23Nine

end
