module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_treesjson " pre:ident jsId:ident : command => do
  let P := pre.getId
  let jN ← liftCoreM <| realizeGlobalConstNoOverload jsId
  let txt ← liftTermElabM <| unsafe evalConst String jN
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "#kss_treesjson: {e}"
  let o ← match j.getObj? with
    | .ok o => pure o
    | .error e => throwError "#kss_treesjson: {e}"
  liftCoreM <| withOptions (Elab.async.set · false) do
    for ⟨k, v⟩ in o.toArray do
      match v.getNat? with
      | Except.ok x => addDef (P ++ Name.mkSimple k) natT (lit x)
      | Except.error _ =>
        match v.getArr? >>= fun a => a.mapM fun x => x.getNat? with
        | Except.ok a => addTree (P ++ Name.mkSimple k) a
        | Except.error e => throwError "#kss_treesjson: {k}: {e}"

end
