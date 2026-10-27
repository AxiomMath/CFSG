module

public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Data.Kernel.Misc.HexFlat
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

open CFSG.KC.Tab in
elab "#kmisc_hexflat " pre:ident sId:ident dd:num nn:num ww:num cn:num : command => do
  let P := pre.getId
  let d := dd.getNat
  let n := nn.getNat
  let w := ww.getNat
  let N := cn.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let b := s.toUTF8
  if b.size < d * n * N then throwError "#kmisc_hexflat: {b.size} bytes, expected {d * n * N}"
  let hv := fun (c : UInt8) => if c.toNat < 58 then c.toNat - 48 else c.toNat - 55
  let vals := Array.ofFn (n := N) fun j => Id.run do
    let mut acc := 0
    for i in [0:n] do
      let v := (List.range d).foldl (fun a t => a * 16 + hv (b.get! (d * (n * j.val + i) + t))) 0
      acc := acc ||| (v <<< (w * i))
    return acc
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree (P ++ `F) vals
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.KC.Misc.HexFlat.hexFlat)
        #[mkConst (P ++ `chars), lit d, lit n, lit w, lit N,
          mkConst (P ++ `F)])
      (mkConst ``Bool.true)
    let nAll := P ++ `all
    CFSG.KC.addThmDecl <| { name := nAll, levelParams := [], type := ty, value := reflBoolTrue }

elab "#kmisc_packarrs " pre:ident sId:ident ww:num : command => do
  let w := ww.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let S ← liftTermElabM <| unsafe evalConst (Array (Array Nat)) sN
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree pre.getId (S.map (CFSG.KS.RawGen.pack w))

elab "#kmisc_sortpair " pre:ident aId:ident bId:ident bb:num nn:num : command => do
  let B := bb.getNat
  let N := nn.getNat
  let aN ← liftCoreM <| realizeGlobalConstNoOverload aId
  let bN ← liftCoreM <| realizeGlobalConstNoOverload bId
  let a ← liftTermElabM <| unsafe evalConst (Array Nat) aN
  let b ← liftTermElabM <| unsafe evalConst (Array Nat) bN
  let key := fun (x : Nat) => B * a[x]! + b[x]!
  let order := ((List.range N).toArray.qsort fun x y => key x < key y)
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KS.RawGen.addTree pre.getId order
