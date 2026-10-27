module

public import CFSG.Certificates.Kernel.Spor.ONKSound
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KS.ONGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def leaves (rb sh : Nat) (xs : Array Nat) : Array Nat := Id.run do
  let per := 1 <<< sh
  let nl := (xs.size + per - 1) / per
  let mut out : Array Nat := Array.mkEmpty nl
  for L in [0:nl] do
    let mut acc := 0
    for r in [0:per] do
      let i := L * per + (per - 1 - r)
      acc := (acc <<< rb) ||| (if i < xs.size then xs[i]! else 0)
    out := out.push acc
  return out

meta def keyOf (w : CFSG.Sporadic.Fi23.Native.W) : Nat :=
  let v := w.toV
  v.p ||| (v.m <<< 256)

meta def encL (l : Int) : Nat := if 0 < l then 2 * (l.toNat - 1) else 2 * ((-l).toNat - 1) + 1

meta def encW : List Int → Nat
  | [] => 0
  | l :: w => encW w + encL l * 16 ^ w.length

end CFSG.KS.ONGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KS.ONGen in
elab "#kon_data " pre:ident oId:ident sId:ident aId:ident bId:ident wId:ident sl:num : command => do
  let P := pre.getId
  let SL := sl.getNat
  let rn := fun (i : Ident) => liftCoreM <| realizeGlobalConstNoOverload i
  let oN ← rn oId
  let sN ← rn sId
  let aN ← rn aId
  let bN ← rn bId
  let wN ← rn wId
  let O ← liftTermElabM <| unsafe evalConst CFSG.Sporadic.ON.Native.VOrbit oN
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  let cA ← liftTermElabM <| unsafe evalConst (Array CFSG.Sporadic.Fi23.Native.W) aN
  let cB ← liftTermElabM <| unsafe evalConst (Array CFSG.Sporadic.Fi23.Native.W) bN
  let words ← liftTermElabM <| unsafe evalConst (Array (List Int)) wN
  let n := O.keys.size
  let keys := O.keys.map keyOf
  let A := O.alpha.map (·.toNat)
  let B := O.beta.map (·.toNat)
  let so := (Array.range n).qsort fun i j => keys[i]! < keys[j]!
  let soi := Id.run do
    let mut r := Array.replicate n 0
    for i in [0:n] do
      r := r.set! so[i]! i
    return r
  let nx := Id.run do
    let mut s := 1
    let mut out : Array Nat := #[]
    for h in [0:n] do
      if h % SL == 0 then out := out.push s
      if A[h]! == s then s := s + 1
      if B[h]! == s then s := s + 1
    out := out.push s
    return out
  let invOf := fun (t : Array Nat) => Id.run do
    let mut r := Array.replicate n 0
    for i in [0:n] do
      r := r.set! t[i]! i
    return r
  withSync do
    addTree (P ++ `K) (leaves 512 4 keys)
    addTree (P ++ `CA) (cA.map keyOf)
    addTree (P ++ `CB) (cB.map keyOf)
    let listE := fun (xs : Array Nat) => xs.toList.foldr (fun x acc =>
      mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc) (mkApp (mkConst ``List.nil [0]) natT)
    addDef (P ++ `LA) (mkApp (mkConst ``List [0]) natT) (listE (cA.map keyOf))
    addDef (P ++ `LB) (mkApp (mkConst ``List [0]) natT) (listE (cB.map keyOf))
    addTree (P ++ `A) (leaves 18 6 A)
    addTree (P ++ `B) (leaves 18 6 B)
    addTree (P ++ `SO) (leaves 18 6 so)
    addTree (P ++ `SOI) (leaves 18 6 soi)
    addTree (P ++ `NX) nx
    for j in [0:S.size] do
      if 2 ≤ j then addTree (P ++ Name.mkSimple s!"T{j}") (leaves 18 6 S[j]!)
      addTree (P ++ Name.mkSimple s!"U{j}") (leaves 18 6 (invOf S[j]!))
    addTree (P ++ `WC) (words.map encW)
    addTree (P ++ `WL) (words.map (·.length))
    addDef (P ++ `n) natT (lit n)
    addDef (P ++ `NS) natT (lit (nx.size - 1))

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kon_slices " fId:ident lo:num hi:num : command => do
  let F ← liftCoreM <| realizeGlobalConstNoOverload fId
  withSync do
    for s in [lo.getNat:hi.getNat] do
      let ty := isTrue (mkApp (mkConst F) (lit s))
      let nm := F.appendAfter (toString s)
      let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
      CFSG.KC.addThmDecl <| { name := nm, levelParams := [], type := ty, value := pf }

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kon_join " nm:ident fId:ident kk:num : command => do
  let F ← liftCoreM <| realizeGlobalConstNoOverload fId
  let k := kk.getNat
  let Pf := mkLambda `s .default natT (isTrue (mkApp (mkConst F) (mkBVar 0)))
  let ty := mkForall `s .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, lit k])
    (isTrue (mkApp (mkConst F) (mkBVar 1))))
  let pf := forallChain Pf k fun s => mkConst (F.appendAfter (toString s))
  withSync do
    CFSG.KC.addThmDecl <| { name := nm.getId, levelParams := [], type := ty, value := pf }

end
