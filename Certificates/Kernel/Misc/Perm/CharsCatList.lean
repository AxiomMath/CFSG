module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.Misc.Perm.CharsCat
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Kernel.Misc.Perm.CharsCat

open Lean Elab Command Meta

public section

namespace CFSG.KS.CharsCatList

theorem nil_eq : ([] : List String) = ([] : List (List Char)).map String.ofList := rfl

theorem cons_eq {a : String} {l : List Char} {as : List String} {ls : List (List Char)}
    (h : a = String.ofList l) (t : as = ls.map String.ofList) :
    a :: as = (l :: ls).map String.ofList := by
  rw [h, t, List.map_cons]

meta partial def listOf (e : Expr) : MetaM (Expr × Expr) := do
  let lcE := mkApp (mkConst ``List [0]) (mkConst ``Char)
  match e with
  | .mdata _ b => listOf b
  | _ =>
    if e.isAppOfArity ``List.nil 1 then
      pure (mkApp (mkConst ``List.nil [0]) lcE, mkConst ``nil_eq)
    else if e.isAppOfArity ``List.cons 3 then
      let a := e.getArg! 1
      let as := e.getArg! 2
      let (l, h) ← CFSG.KS.CharsCat.charsOf a
      let (ls, t) ← listOf as
      pure (mkApp3 (mkConst ``List.cons [0]) lcE l ls, mkAppN (mkConst ``cons_eq) #[a, l, as, ls, h, t])
    else
      throwError "#ks_chars_cat_list: not a list literal: {e}"

end CFSG.KS.CharsCatList

elab "#ks_chars_cat_list " pre:ident tId:ident : command => do
  let P := pre.getId
  let tN ← liftCoreM <| realizeGlobalConstNoOverload tId
  let some body := ((← getEnv).find? tN).bind ConstantInfo.value?
    | throwError "#ks_chars_cat_list: {tN} has no value"
  let (ls, pf) ← liftTermElabM do CFSG.KS.CharsCatList.listOf (← Meta.zetaReduce body)
  let lcE := mkApp (mkConst ``List [0]) (mkConst ``Char)
  let lty := mkApp (mkConst ``List [0]) lcE
  liftCoreM <| withOptions (Elab.async.set · false) do
    CFSG.KC.Tab.addDef (P ++ `chars) lty ls
    let rhs := mkAppN (mkConst ``List.map [0, 0]) #[lcE, mkConst ``String, mkConst ``String.ofList,
      mkConst (P ++ `chars)]
    let ty := mkApp3 (mkConst ``Eq [1]) (mkApp (mkConst ``List [0]) (mkConst ``String)) (mkConst tN) rhs
    CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }

end
