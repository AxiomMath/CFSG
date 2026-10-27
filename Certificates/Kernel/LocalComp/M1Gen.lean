module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.M1F2
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.KC.M1Gen

open CFSG.KC.Tab

meta def decode (d : Nat) (s : String) : Nat := Id.run do
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let ws (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 ||
    c.toNat == 12
  let es := (body.filter fun c => !ws c).map fun c =>
    if '0' ≤ c && c ≤ '9' then (c.toNat - '0'.toNat) % 2 else 0
  let mut acc := 0
  let mut k := 0
  for e in es do
    if k < d * d && e == 1 then acc := acc ||| (1 <<< k)
    k := k + 1
  return acc

elab "#lc_m1 " pre:ident sId:ident dN:num : command => do
  let P := pre.getId
  let d := dN.getNat
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  let M := decode d s
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (P ++ `M) (mkConst ``Nat) (mkRawNatLit M)
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkApp3 (mkConst ``CFSG.KC.M1F2.m1Bind) (mkConst (P ++ `chars)) (mkRawNatLit d)
        (mkConst (P ++ `M))) (mkConst ``Bool.true)
    CFSG.KC.addThmDecl <| { name := P ++ `bind, levelParams := [], type := ty, value := reflBoolTrue }

elab "#lc_m1mat " pre:ident sId:ident dN:num : command => do
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let s ← liftTermElabM <| unsafe evalConst String sN
  liftCoreM <| withOptions (Elab.async.set · false) do
    addDef (pre.getId ++ `M) (mkConst ``Nat) (mkRawNatLit (decode dN.getNat s))

end CFSG.KC.M1Gen

end
