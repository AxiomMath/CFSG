module

public meta import CFSG.RankThree.Native.ONSevenArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public meta import CFSG.Certificates.NativeSchreierCard
public meta import CFSG.Sporadic.Schreier.ONCheckChain
public import Certificates.Data.CFSGNative.ONSchreier.Compact
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CertificateChecks.KernelSpor.ONS.Gen

open CFSG.ONSchreier CFSG.ONSchreier.Native

structure Ctx where
  S : Array (Array Nat)
  Si : Array (Array Nat)
  st1 : Array (Array Nat)
  st2 : Array (Array Nat)
  it1 : Array (Array Nat)
  L1 : CLevel
  L2 : CLevel

meta def mkCtx : Ctx :=
  let S := qonStrongArrs
  let Si := pinvs 245520 S
  let base := Data.baseList.toArray
  let st := allSteps S Si base
  let it := allInvSteps S Si base
  ⟨S, Si, st[1]!, st[2]!, it[1]!, cbfs 245520 base[1]! st[1]!, cbfs 245520 base[2]! st[2]!⟩

meta def wimg (c : Ctx) (w : List Int) (x : Nat) : Nat :=
  w.foldr (fun (l : Int) (y : Nat) =>
    if 0 < l then (c.S[l.toNat - 1]!)[y]! else (c.Si[(-l).toNat - 1]!)[y]!) x

meta partial def trA (st : Array (Array Nat)) (L : CLevel) (k p : Nat) : Nat :=
  if k == 0 then p else (st[L.lab[k]!]!)[trA st L L.par[k]! p]!

meta partial def trI (it : Array (Array Nat)) (L : CLevel) (k p : Nat) : Nat :=
  if k == 0 then p else trI it L L.par[k]! ((it[L.lab[k]!]!)[p]!)

meta def aList (c : Ctx) (z : List Int) : List Nat :=
  (List.range 36).map fun k => trA c.st2 c.L2 k (wimg c z 227759)

meta def ccVal (c : Ctx) (z : List Int) (A : Array Nat) (zb : Nat) (k : Nat) : Nat :=
  if k < 52136 then
    let v := trI c.it1 c.L1 k (wimg c z (trA c.st1 c.L1 k 227759))
    ((List.range 36).filter fun k₂ => A[k₂]! == v &&
      trA c.st1 c.L1 k (trA c.st2 c.L2 k₂ zb) ==
        wimg c z (trA c.st1 c.L1 k (trA c.st2 c.L2 k₂ 100817))).length
  else 0

meta def ccSlices (c : Ctx) (z : List Int) : List Nat :=
  let A := (aList c z).toArray
  let zb := wimg c z 100817
  (List.range 26).map fun s =>
    ((List.range 2048).map fun i => ccVal c z A zb (2048 * s + i)).foldl (· + ·) 0

meta def fixSlices (c : Ctx) (x t : List Int) (bad : List Nat) : List Nat :=
  (List.range 8).map fun s =>
    ((List.range 30720).filter fun i =>
      let p := 30720 * s + i
      p < 245520 && wimg c x p == p && !(bad.contains (wimg c t p))).length

end CertificateChecks.KernelSpor.ONS.Gen

end
