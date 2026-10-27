module

public import Certificates.Data.Kernel.Fi23R.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Sporadic.Fi23Br.Words
public import Certificates.Data.BabyTwoBD0

public section

namespace CFSG.KD.Fi23BD0

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native

@[expose] def rW (w : List Nat) : List Nat := w.map (Nat.add (nat_lit 52))

@[expose] def rZ (z : Int) : Nat :=
  if z = 2 then 40 else if z = -2 then 41 else 39

@[expose] noncomputable def t3W : List Nat :=
  (CFSG.KD.BrFi23.IT.W.toArray[2]!).map rZ ++ (CFSG.KD.BrFi23.IT.W.toArray[3]!).map rZ

@[expose] noncomputable def yImg (Y : Nat → List Nat) (a b c e t : Nat) : Nat :=
  wv G (powW a (Y 0)) (wv G (powW b (Y 1)) (wv G (powW c (Y 2)) (wv G (powW e (Y 3)) t)))

@[expose] noncomputable def bD0KW (Y : Nat → List Nat) (C T : List Nat) : Bool :=
  allN (nat_lit 4) (fun i => allN (nat_lit 4) fun j => allN (nat_lit 6) fun t =>
      Nat.beq (wv G (Y i) (wv G (Y j) t)) (wv G (Y j) (wv G (Y i) t))) &&
    allN (nat_lit 4) (fun i => allN (nat_lit 6) fun t => Nat.beq (wv G (powW 3 (Y i)) t) t) &&
    allN (nat_lit 4) (fun i => allN (nat_lit 2) fun k =>
      Nat.beq (wv G (Y i) kleinPts[k]!) kleinPts[k]!) &&
    allN (nat_lit 3) (fun a => allN (nat_lit 3) fun b => allN (nat_lit 3) fun c =>
      allN (nat_lit 3) fun e =>
        Nat.beq (a + b + c + e) 0 || !(allN (nat_lit 6) fun t => Nat.beq (yImg Y a b c e t) t)) &&
    allN (nat_lit 6) (fun t => Nat.beq (wv G C (wv G (Y 0) t)) (wv G T (wv G C t)))

@[expose] noncomputable def bD0K : Bool :=
  bD0KW (fun i => rW bD0Words[i]!) (rW bD0Conj) t3W

end CFSG.KD.Fi23BD0

end
