module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab in
elab "#kmisc_hexflat_tab " pre:ident sId:ident dd:num nn:num ww:num cn:num : command => do
  let P := pre.getId
  let d := dd.getNat
  let n := nn.getNat
  let w := ww.getNat
  let N := cn.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size < d * n * N then throwError "#kmisc_hexflat_tab: {b.size} bytes, expected {d * n * N}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let vals := Array.ofFn (n := N) fun j => Id.run do
    let mut acc := 0
    for i in [0:n] do
      let v := (List.range d).foldl (fun a t => a * 16 + hv (b.get! (d * (n * j.val + i) + t))) 0
      acc := acc ||| (v <<< (w * i))
    return acc
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree (P ++ `F) vals

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#ks_hexlines_tab " pre:ident sId:ident wdN:num nN:num wN:num : command => do
  let P := pre.getId
  let wd := wdN.getNat
  let n := nN.getNat
  let w := wN.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let hexv := fun (c : Char) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let ls := (s.splitOn "\n").filter (· ≠ "")
  let vals := ls.toArray.map fun l =>
    let cs := l.toList.toArray
    pack w (Array.ofFn (n := n) fun i => (List.range wd).foldl (fun acc t => acc * 16 +
      hexv cs[wd * i.val + t]!) 0)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `L) vals
    addDef (P ++ `lines) natT (lit vals.size)
