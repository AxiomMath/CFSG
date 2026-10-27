module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Lean

open Lean Elab Command

namespace CFSG.KS.GenMask

meta def products (Ls : Array CFSG.Monster.B.Co2.Native.Level) (n : Nat) : Array (Nat × Array Nat) := Id.run do
  let c := (List.range 5).map fun i => Ls[i]!.pts.size
  let mut out : Array (Nat × Array Nat) := #[]
  for a in [0:c[0]!] do
    for b in [0:c[1]!] do
      let tab := CFSG.KS.RawGen.comp n Ls[0]!.tr[a]! Ls[1]!.tr[b]!
      for cc in [0:c[2]!] do
        let tabc := CFSG.KS.RawGen.comp n tab Ls[2]!.tr[cc]!
        for d in [0:c[3]!] do
          let t3 := CFSG.KS.RawGen.comp n tabc Ls[3]!.tr[d]!
          for e in [0:c[4]!] do
            let g := CFSG.KS.RawGen.comp n t3 Ls[4]!.tr[e]!
            out := out.push ((((a * c[1]! + b) * c[2]! + cc) * c[3]! + d) * c[4]! + e, g)
  return out

meta def maskOfL (C : List Nat) : Nat := C.foldl (fun m k => m ||| (1 <<< k)) 0

end CFSG.KS.GenMask

open CFSG.KC.Tab CFSG.KS.GenMask CFSG.KS.RawGen in
elab "#kst_mask " pre:ident lId:ident xId:ident : command => do
  let lN ← liftCoreM <| realizeGlobalConstNoOverload lId
  let xN ← liftCoreM <| realizeGlobalConstNoOverload xId
  let Ls ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) lN
  let X ← liftTermElabM <| unsafe evalConst (Array Nat) xN
  let n := X.size
  let C := ((products Ls n).filter fun (_, g) => comp n g X == comp n X g).toList.map (·.1)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (pre.getId ++ `M) natT (lit (maskOfL C))

open CFSG.KC.Tab CFSG.KS.GenMask CFSG.KS.RawGen in
elab "#kst_maskN " pre:ident lId:ident xId:ident qId:ident : command => do
  let P := pre.getId
  let lN ← liftCoreM <| realizeGlobalConstNoOverload lId
  let xN ← liftCoreM <| realizeGlobalConstNoOverload xId
  let qN ← liftCoreM <| realizeGlobalConstNoOverload qId
  let Ls ← liftTermElabM <| unsafe evalConst (Array CFSG.Monster.B.Co2.Native.Level) lN
  let X ← liftTermElabM <| unsafe evalConst (Array Nat) xN
  let q ← liftTermElabM <| unsafe evalConst (Array Nat → Bool) qN
  let n := X.size
  let base := (List.range 5).map fun i => Ls[i]!.pts[0]!
  let S := (products Ls n).filter fun (_, g) => comp n g X == comp n X g
  let SK := S.filter fun (_, g) => q g
  let SC := S.filter fun (_, g) => SK.all fun (_, h) => base.all fun b => g[h[b]!]! == h[g[b]!]!
  let mut idx : Std.HashMap (Array Nat) Nat := {}
  for j in [0:SK.size] do
    idx := idx.insert SK[j]!.2 j
  let mut gens : Array (Nat × Array Nat) := #[]
  let mut W : Array (Nat × Nat) := #[]
  for i in [1:SK.size] do
    let (c, q) := SK[i]!
    let mut found : Option (Nat × Nat) := none
    for (gc, g) in gens do
      if found.isNone then
        match idx.get? (comp n (inv n g) q) with
        | some j => if j < i then found := some (gc, SK[j]!.1)
        | none => pure ()
    match found with
    | some w => W := W.push w
    | none =>
      gens := gens.push (c, q)
      W := W.push (c, SK[0]!.1)
  let pairT := mkApp2 (mkConst ``Prod [0, 0]) natT natT
  let pairsE := W.toList.foldr (fun (a, b) acc => mkApp3 (mkConst ``List.cons [0]) pairT
    (mkApp4 (mkConst ``Prod.mk [0, 0]) natT natT (lit a) (lit b)) acc)
    (mkApp (mkConst ``List.nil [0]) pairT)
  let ltyE := mkApp (mkConst ``List [0]) natT
  let listE := fun (xs : List Nat) => xs.foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc) (mkApp (mkConst ``List.nil [0]) natT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `M) natT (lit (maskOfL (S.toList.map (·.1))))
    addDef (P ++ `MK) natT (lit (maskOfL (SK.toList.map (·.1))))
    addDef (P ++ `CK) ltyE (listE (SK.toList.map (·.1)))
    addDef (P ++ `MC) natT (lit (maskOfL (SC.toList.map (·.1))))
    addDef (P ++ `GC) ltyE (listE (gens.toList.map (·.1)))
    addDef (P ++ `W) (mkApp (mkConst ``List [0]) pairT) pairsE
