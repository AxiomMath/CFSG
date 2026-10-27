module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.SporSch.GenSetReplay
public meta import CFSG.Sporadic.HNSchreier.Data
public import CFSG.Certificates.Kernel.SporSch.HNXOrbSound
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.SporSch.HNXOrb
public import Lean.Exception
public meta import Mathlib.Init

open Lean Elab Command

public section

namespace CFSG.KS.SporSchGen

meta partial def strLits (e : Expr) (acc : Array String) : Array String :=
  match e with
  | .lit (.strVal s) => acc.push s
  | .app f a => strLits a (strLits f acc)
  | .mdata _ b => strLits b acc
  | _ => acc

end CFSG.KS.SporSchGen

open CFSG.KC.Tab CFSG.KS.SporSchGen in
elab "#kss_strlits " pre:ident cId:ident : command => do
  let P := pre.getId
  let cN ← liftCoreM <| realizeGlobalConstNoOverload cId
  let env ← getEnv
  let some ci := env.find? cN | throwError "unknown constant"
  let some val := ci.value? | throwError "no value"
  let lits := strLits val #[]
  let charE : Expr := mkConst ``Char
  let mk (ch : Char) : Expr := mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)
  let lty := mkApp (mkConst ``List [0]) charE
  let strT := mkConst ``String
  liftCoreM <| withOptions (Elab.async.set · false) do
    for k in [0:lits.size] do
      let s := lits[k]!
      let lst := s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charE (mk ch) acc)
        (mkApp (mkConst ``List.nil [0]) charE)
      let cn := P ++ Name.mkSimple s!"c{k}"
      addDef cn lty lst
      let ofL := mkApp (mkConst ``String.ofList) (mkConst cn)
      let en := P ++ Name.mkSimple ("e" ++ toString k)
      let ety := mkApp3 (mkConst ``Eq [1]) strT (mkStrLit s) ofL
      let ev := mkApp2 (mkConst ``Eq.refl [1]) strT (mkStrLit s)
      CFSG.KC.addThmDecl <| { name := en, levelParams := [], type := ety, value := ev }

end
