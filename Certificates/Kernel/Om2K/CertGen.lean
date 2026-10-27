module

public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Monster.B.Fischer.ArrCert
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Monster.B.Fischer.ArrCert
public meta import Lean
public meta import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Std.Data.HashMap

open Lean Elab Command

public section

namespace CFSG.KC.CertGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Monster.B.Fischer

meta def maskOf (a : Array Nat) : Nat := a.foldl (fun m x => m ||| (1 <<< x)) 0

meta def parLab (c : ArrCert) : Array Nat :=
  (Array.range c.pts.size).map fun i => c.par[i]! ||| (c.lab[i]! <<< 16)

meta def clog2 (n : Nat) : Nat := Id.run do
  let mut h := 0
  while (1 <<< h) < n do h := h + 1
  return h

meta def addGrouped (F : Name) (vs : Array Nat) (ω lg : Nat) : CoreM Unit := do
  let g := 1 <<< lg
  let nl := max ((vs.size + g - 1) / g) 1
  let h := clog2 nl
  addDef (F ++ `Z) natT (lit 0)
  for j in [0:nl] do
    addDef (F ++ Name.mkSimple s!"L{j}") natT (lit (pack ω (vs.extract (j * g) (j * g + g))))
  let leaf := fun (j : Nat) =>
    let L := if j < nl then mkConst (F ++ Name.mkSimple s!"L{j}") else mkConst (F ++ `Z)
    mkLambda `i .default natT (mkAppN (mkConst ``CFSG.KC.Enum.pg)
      #[lit ω, lit ((1 <<< ω) - 1), L, mkApp2 (mkConst ``Nat.land) (mkBVar 0) (lit (g - 1))])
  addDef F fnT (table leaf (1 <<< h) lg)

meta def addIdx (P : Name) (c r : ArrCert) : CoreM Unit := do
  let mut idx : Std.HashMap Nat Nat := {}
  for j in [0:r.pts.size] do
    idx := idx.insert (maskOf r.pts[j]!) j
  let mut xs : Array Nat := #[]
  for p in c.pts do
    match idx.get? (maskOf p) with
    | some j => xs := xs.push j
    | none => throwError "#arr_certs_idx: a point is not a point of the reference certificate"
  let mut ys : Array Nat := Array.replicate r.pts.size c.pts.size
  for i in [0:xs.size] do
    ys := ys.set! xs[i]! i
  let ng := (c.edges.foldl (fun m e => max m e.size) 0)
  addDef (P ++ `N) natT (lit c.pts.size)
  addGrouped (P ++ `X) xs 16 6
  addGrouped (P ++ `Y) ys 16 6
  addGrouped (P ++ `E) (c.edges.map (pack 16)) (16 * max ng 1) 2
  addGrouped (P ++ `D) (parLab c) 32 5

end CFSG.KC.CertGen

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.CertGen in
elab "#arr_cert_tabs " pre:ident cId:ident w:num kb:num : command => do
  let P := pre.getId
  let w := w.getNat
  let kb := kb.getNat
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let c ← liftTermElabM <| unsafe evalConst CFSG.Monster.B.Fischer.ArrCert cN
  let ng := (c.edges.foldl (fun m e => max m e.size) 0)
  let keys := c.pts.map fun p => p.foldl (fun acc i => acc * kb + i) 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `N) natT (lit c.pts.size)
    addTree (P ++ `C) (c.pts.map (pack w))
    addTree (P ++ `M) (c.pts.map maskOf)
    addGrouped (P ++ `E) (c.edges.map (pack 16)) (16 * max ng 1) 2
    addGrouped (P ++ `D) (parLab c) 32 5
    addGrouped (P ++ `S) ((Array.range keys.size).qsort fun a b => keys[a]! < keys[b]!) 16 6

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.CertGen in
elab "#perm_tab " pre:ident gId:ident w:num : command => do
  let P := pre.getId
  let w := w.getNat
  let gN ← liftCoreM <| realizeGlobalConstNoOverload gId
  let gs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) gN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `G) (gs.toArray.map (pack w))
    addDef (P ++ `ng) natT (lit gs.length)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.KC.CertGen in
elab "#arr_certs_idx " pre:ident cId:ident rId:ident : command => do
  let P := pre.getId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let rN ← liftCoreM <| realizeGlobalConstNoOverload rId
  let cs ← liftTermElabM <| unsafe evalConst (List CFSG.Monster.B.Fischer.ArrCert) cN
  let r ← liftTermElabM <| unsafe evalConst CFSG.Monster.B.Fischer.ArrCert rN
  liftCoreM <| withOptions (Elab.async.set · false) do
    let mut k := 0
    for c in cs do
      addIdx (P ++ Name.mkSimple s!"c{k}") c r
      k := k + 1

end
