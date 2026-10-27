module

public import CFSG.Certificates.Kernel.Spor.ONKFSound
public meta import CFSG.Certificates.Kernel.Common.Tab
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Lean
public import CFSG.Certificates.Kernel.Common.AddThm
public import Certificates.Kernel.Sporadic.RawGen
public import Lean.Exception

open Lean Elab Command

public section

namespace CFSG.KS.ONFGen

open CFSG.KC.Tab CFSG.KS.RawGen

meta def addPN (ap am bp bm : Nat) : Nat :=
  ((ap ^^^ (ap &&& (bp ||| bm))) ||| (bp ^^^ (bp &&& (ap ||| am)))) ||| (am &&& bm)

meta def addMN (ap am bp bm : Nat) : Nat :=
  ((am ^^^ (am &&& (bp ||| bm))) ||| (bm ^^^ (bm &&& (ap ||| am)))) ||| (ap &&& bp)

meta def mvLN : List Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | [], _, _, ap, am => (ap, am)
  | c :: L, xp, xm, ap, am =>
    let cp := c &&& ((1 <<< 256) - 1)
    let cm := c >>> 256
    if xp &&& 1 == 1 then mvLN L (xp >>> 1) (xm >>> 1) (addPN ap am cp cm) (addMN ap am cp cm)
    else if xm &&& 1 == 1 then mvLN L (xp >>> 1) (xm >>> 1) (addPN ap am cm cp) (addMN ap am cm cp)
    else mvLN L (xp >>> 1) (xm >>> 1) ap am

meta def chunks4 : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _, [] => []
  | f + 1, L => L.take 4 :: chunks4 f (L.drop 4)

meta def leavesOf (seed : Nat) (cs : List (List Nat)) : Array Nat := Id.run do
  let mut out := #[]
  for C in cs do
    for xm in [0:16] do
      let mut T := 0
      for xp in [0:16] do
        let (p, m) := mvLN C xp xm 0 0
        let s := ((out.size * 16 + xp + 1) * 0x9E3779B97F4A7C15 * (seed + 7)) % 2 ^ 128
        let sp := (s >>> 3) % 2 ^ 64
        let sm := ((s >>> 67) ^^^ (s * 0xBF58476D1CE4E5B9)) % 2 ^ 64
        T := T ||| (((sp ||| (p <<< 64)) ||| ((sm ||| (m <<< 64)) <<< 224)) <<< (448 * xp))
      out := out.push T
  return out

elab "#konf_slices " fId:ident gId:ident lo:num hi:num : command => do
  let F ← liftCoreM <| realizeGlobalConstNoOverload fId
  let G ← liftCoreM <| realizeGlobalConstNoOverload gId
  let rflT := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  withSync do
    for s in [lo.getNat:hi.getNat] do
      let ty := isTrue (mkApp (mkConst F) (lit s))
      let pf := mkApp2 (mkConst G) (lit s) rflT
      CFSG.KC.addThmDecl <| { name := F.appendAfter (toString s), levelParams := [], type := ty, value := pf }

end CFSG.KS.ONFGen
