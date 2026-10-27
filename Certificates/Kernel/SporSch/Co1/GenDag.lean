module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

public section

open CFSG.KC.Tab CFSG.KS.RawGen in
elab "#kss_co1dag " pre:ident dId:ident : command => do
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let D ← liftTermElabM <| unsafe evalConst
    (List (Array Nat) × List (Array Nat) × Bool) dN
  let P := pre.getId
  liftCoreM <| withOptions (Elab.async.set · false) do
    addTree (P ++ `M) (D.1.toArray.map (pack 24))
    addTree (P ++ `MI) (D.2.1.toArray.map (pack 24))
    addDef (P ++ `N) natT (lit D.1.length)

open CFSG.KC.Tab CFSG.KS.RawGen CFSG.Sporadic.Co1Schreier.Native in
elab "#kss_co1sortE " pre:ident dId:ident iId:ident : command => do
  let dN ← liftCoreM <| realizeGlobalConstNoOverload dId
  let iN ← liftCoreM <| realizeGlobalConstNoOverload iId
  let D ← liftTermElabM <| unsafe evalConst
    (List (Array Nat) × List (Array Nat) × Bool) dN
  let I ← liftTermElabM <| unsafe evalConst (List Nat) iN
  let P := pre.getId
  let a := fun (i : Nat) => D.1.getD (I.getD i 0) (one ())
  let e := fun (n : Nat) => pack 24 <|
    (List.range 6).foldr (fun i acc => mul (pow (a i) (n / 3 ^ i % 3)) acc) (one ())
  let Ms := (List.range 729).toArray.qsort fun x y => e x < e y
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `MsP) natT (lit (pack 10 Ms))

end
