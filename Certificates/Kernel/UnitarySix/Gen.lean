module

public import Certificates.Data.Kernel.U6.Core
public meta import Certificates.Data.CFSGNative.F4.Unitary
public meta import Certificates.Data.CFSGNative.Fischer.Polar
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.U6.Tables
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean

open Lean Elab Command

public section

namespace CFSG.KC.U6Gen

open CFSG.KC.Tab

meta def packW (w : Nat) (a : Array Nat) : Nat := Id.run do
  let mut acc := 0
  for i in [0:a.size] do
    acc := acc ||| (a[i]! <<< (w * i))
  return acc

elab "#u6_pts " pre:ident : command => do
  let P := pre.getId
  let up := CFSG.F4.Native.uPts
  let ps := CFSG.F4.Native.uPos
  let tv := CFSG.F4.Native.tvGens
  let lt := (Array.range 46).map fun k =>
    packW 10 ((CFSG.F4.Native.tvTable tv[k]!).map UInt32.toNat)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `UP) (mkConst ``Nat) (mkRawNatLit (packW 12 up))
    addDef (P ++ `POS) (mkConst ``Nat) (mkRawNatLit (packW 10 ps))
    addDef (P ++ `TV) (mkConst ``Nat) (mkRawNatLit (packW 12 tv))
    addDef (P ++ `LT) (mkConst ``Nat) (mkRawNatLit (packW 6930 lt))

open CFSG.KS.RawGen in
elab "#u6_tables " pre:ident : command => do
  let P := pre.getId
  let up := CFSG.F4.Native.uPts
  let ps := CFSG.F4.Native.uPos
  let posn := (Array.range 4096).map fun c => ps[CFSG.F4.Native.normC c]!
  let mv := (Array.range (693 * 4)).map fun i => CFSG.F4.Native.scaleC (i % 4) up[i / 4]!
  let rows := CFSG.Fischer.Native.tvTabs.map fun t => packW 10 (t.map UInt32.toNat)
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `POSN) (mkConst ``Nat) (mkRawNatLit (packW 10 posn))
    addDef (P ++ `MVT) (mkConst ``Nat) (mkRawNatLit (packW 12 mv))
    addTree (P ++ `R) rows

end CFSG.KC.U6Gen

end
