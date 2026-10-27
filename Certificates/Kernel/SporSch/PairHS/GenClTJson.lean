module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.PairClT
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_cltjson " pre:ident jsId:ident key:str : command => do
  let P := pre.getId
  let k := key.getString
  let jN ← liftCoreM <| realizeGlobalConstNoOverload jsId
  let txt ← liftTermElabM <| unsafe evalConst String jN
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "#kss_cltjson: {e}"
  let o ← match j.getObjVal? k with
    | .ok o => pure o
    | .error e => throwError "#kss_cltjson: {k}: {e}"
  let nats : Json → Except String (Array Nat) := fun v => do
    let a ← v.getArr?
    a.mapM fun x => x.getNat?
  liftCoreM <| withOptions (Elab.async.set · false) do
    for t in ["Ts", "LT", "PT", "QT", "XT", "WT", "KT", "C", "ST", "SIT"] do
      match o.getObjVal? t with
      | Except.ok v =>
        match nats v with
        | Except.ok a => addTree (P ++ Name.mkSimple t) a
        | Except.error e => throwError "#kss_cltjson: {k}.{t}: {e}"
      | Except.error _ => pure ()
    for t in ["NR", "kw", "c", "nS", "nB"] do
      match o.getObjVal? t with
      | Except.ok v =>
        match v.getNat? with
        | Except.ok x => addDef (P ++ Name.mkSimple t) natT (lit x)
        | Except.error e => throwError "#kss_cltjson: {k}.{t}: {e}"
      | Except.error _ => pure ()

end
