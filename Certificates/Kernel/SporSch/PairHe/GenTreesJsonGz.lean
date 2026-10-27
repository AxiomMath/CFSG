module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_treesjsongz " pre:ident path:str size:num hash:num : command => do
  let P := pre.getId
  let b ← CFSG.KC.Gz.readPinnedGz path.getString size.getNat hash.getNat
  let some txt := String.fromUTF8? b | throwError "#kss_treesjsongz: {path.getString}: not UTF-8"
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throwError "#kss_treesjsongz: {e}"
  let o ← match j.getObj? with
    | .ok o => pure o
    | .error e => throwError "#kss_treesjsongz: {e}"
  liftCoreM <| withOptions (Elab.async.set · false) do
    for ⟨k, v⟩ in o.toArray do
      match v.getNat? with
      | Except.ok x => addDef (P ++ Name.mkSimple k) natT (lit x)
      | Except.error _ =>
        match v.getArr? >>= fun a => a.mapM fun x => x.getNat? with
        | Except.ok a => addTree (P ++ Name.mkSimple k) a
        | Except.error e => throwError "#kss_treesjsongz: {k}: {e}"

end
