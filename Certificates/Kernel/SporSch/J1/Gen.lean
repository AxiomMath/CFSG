module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_sortorder " pre:ident ww:num aId:ident : command => do
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let A ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) aN
  let codes := A.map (pack ww.getNat)
  let ord := ((List.range A.size).toArray.qsort fun i j => codes[i]! < codes[j]!).toList
  let natE := natT
  let lst := ord.foldr (fun k acc => mkApp3 (mkConst ``List.cons [0]) natE (lit k) acc)
    (mkApp (mkConst ``List.nil [0]) natE)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef pre.getId (mkApp (mkConst ``List [0]) natE) lst

end
