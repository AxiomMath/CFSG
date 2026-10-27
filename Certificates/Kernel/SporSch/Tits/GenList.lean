module

public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean

open Lean Elab Command

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kst_plist " pre:ident ww:num xId:ident : command => do
  let P := pre.getId
  let w := ww.getNat
  let xN ← liftCoreM <| realizeGlobalConstNoOverload xId
  let Xs ← liftTermElabM <| unsafe evalConst (List (Array Nat)) xN
  let listE := (Xs.map (pack w)).foldr (fun x acc =>
    mkApp3 (mkConst ``List.cons [0]) natT (lit x) acc) (mkApp (mkConst ``List.nil [0]) natT)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef P (mkApp (mkConst ``List [0]) natT) listE
