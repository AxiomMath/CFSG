module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

elab "#kmisc_tree " pre:ident src:ident dd:num cn:num : command => do
  let d := dd.getNat
  let cnt := cn.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload src
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size != d * cnt then throwError "#kmisc_tree: {b.size} digits, expected {d * cnt}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 87
  let vals := Array.ofFn (n := cnt) fun i =>
    (List.range d).foldl (fun acc t => acc * 16 + hv (b.get! (d * i.val + t))) 0
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree pre.getId vals

open CFSG.KC.Tab in
elab "#kmisc_treeg " pre:ident src:ident dd:num cn:num gg:num : command => do
  let d := dd.getNat
  let cnt := cn.getNat
  let g := gg.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload src
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size != d * cnt then throwError "#kmisc_treeg: {b.size} digits, expected {d * cnt}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 87
  let vals := Array.ofFn (n := cnt) fun i =>
    (List.range d).foldl (fun acc t => acc * 16 + hv (b.get! (d * i.val + t))) 0
  let ng := (cnt + g - 1) / g
  let packs := Array.ofFn (n := ng) fun j =>
    (List.range g).foldl (fun acc t => acc ||| ((vals.getD (g * j.val + t) 0) <<< (4 * d * t))) 0
  let P := pre.getId
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree (P ++ `T) packs
    let k := mkBVar 0
    let gE := mkRawNatLit g
    let wE := mkRawNatLit (4 * d)
    let body := mkApp3 (mkConst `CFSG.KC.Ord.bitsN)
      (mkApp (mkConst (P ++ `T)) (mkApp2 (mkConst ``Nat.div) k gE))
      (mkApp2 (mkConst ``Nat.mul) wE (mkApp2 (mkConst ``Nat.mod) k gE)) wE
    addDef P fnT (mkLambda `k .default natT body)
