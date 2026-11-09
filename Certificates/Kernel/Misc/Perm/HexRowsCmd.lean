module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab in
elab "#kmisc_hexflat_rows " pre:ident sId:ident mm:num dd:num nn:num ww:num cn:num :
    command => do
  let P := pre.getId
  let m := mm.getNat
  let d := dd.getNat
  let n := nn.getNat
  let w := ww.getNat
  let N := cn.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size < m + d * n * N then
    throwError "#kmisc_hexflat_rows: {b.size} bytes, expected {m + d * n * N}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let vals := Array.ofFn (n := N) fun j => Id.run do
    let mut acc := 0
    for i in [0:n] do
      let v := (List.range d).foldl
        (fun a t => a * 16 + hv (b.get! (m + d * (n * j.val + i) + t))) 0
      acc := acc ||| (v <<< (w * i))
    return acc
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree (P ++ `F) vals
