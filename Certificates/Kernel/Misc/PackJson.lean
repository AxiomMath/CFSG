module

public meta import Lean
public meta import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Common.HarnessGz
meta import all CFSG.Certificates.Kernel.Common.HarnessGz
public import Certificates.Kernel.Sporadic.RawGen

open Lean Elab Command

namespace CFSG.KC.PackJson

meta def natOf (j : Json) : Except String Nat :=
  match j with
  | .num n => if n.exponent == 0 && n.mantissa ≥ 0 then .ok n.mantissa.toNat
    else .error s!"expected a natural number, got {j}"
  | _ => .error s!"expected a natural number, got {j}"

meta def entries (j : Json) (x : String) (w : Nat) : Except String (Array Nat) := do
  let .arr xs ← j.getObjVal? x | .error s!"member {x} is not an array"
  if w == 0 then xs.mapM natOf
  else xs.mapM fun e => do
    let .arr ys := e | .error s!"member {x}: expected an array of arrays"
    let vs ← ys.mapM natOf
    return CFSG.KS.RawGen.pack w vs

end CFSG.KC.PackJson

open CFSG.KC.Gz CFSG.KC.PackJson in
elab "#kmisc_json_pack " pre:ident path:str size:num hash:num
    fs:("(" ident ident num ")")* : command => do
  let b ← readPinnedGz path.getString size.getNat hash.getNat
  let some s := String.fromUTF8? b | throwError "#kmisc_json_pack: {path.getString} is not UTF-8"
  let j ← match Json.parse s with
    | .ok j => pure j
    | .error e => throwError "#kmisc_json_pack: {path.getString}: {e}"
  for f in fs do
    let x : Ident := ⟨f.raw[1]⟩
    let t : Ident := ⟨f.raw[2]⟩
    let w := (⟨f.raw[3]⟩ : TSyntax `num).getNat
    let vs ← match entries j x.getId.toString w with
      | .ok vs => pure vs
      | .error e => throwError "#kmisc_json_pack: {e}"
    liftCoreM <| withOptions (Elab.async.set · false) do
      CFSG.KS.RawGen.addTree (pre.getId ++ t.getId) vs
