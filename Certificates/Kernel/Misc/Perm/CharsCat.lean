module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

open Lean Elab Command Meta

public section

namespace CFSG.KS.CharsCat

meta def listE (cs : List Char) : Expr :=
  cs.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char)
      (mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Char))

meta partial def charsOf (e : Expr) : MetaM (Expr × Expr) := do
  match e with
  | .lit (.strVal s) =>
    let l := listE s.toList
    pure (l, ← mkEqRefl e)
  | .mdata _ b => charsOf b
  | _ =>
    unless e.isAppOfArity ``HAppend.hAppend 6 do
      throwError "#ks_chars_cat: not a `++` of string literals: {e}"
    let (la, pa) ← charsOf (e.getArg! 4)
    let (lb, pb) ← charsOf (e.getArg! 5)
    let h1 ← mkCongr (← mkCongrArg e.appFn!.appFn! pa) pb
    let h2 ← mkEqSymm (← mkAppOptM ``String.ofList_append #[some la, some lb])
    pure (← mkAppM ``HAppend.hAppend #[la, lb], ← mkEqTrans h1 h2)

end CFSG.KS.CharsCat

elab "#ks_chars_cat " pre:ident sId:ident : command => do
  let P := pre.getId
  let sN ← liftCoreM <| realizeGlobalConstNoOverload sId
  let some body := ((← getEnv).find? sN).bind ConstantInfo.value?
    | throwError "#ks_chars_cat: {sN} has no value"
  let (l, pf) ← liftTermElabM <| CFSG.KS.CharsCat.charsOf body
  let lty := mkApp (mkConst ``List [0]) (mkConst ``Char)
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KC.Tab.addDef (P ++ `chars) lty l
    let ty := mkApp3 (mkConst ``Eq [1]) (mkConst ``String) (mkConst sN)
      (mkApp (mkConst ``String.ofList) (mkConst (P ++ `chars)))
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }

end
