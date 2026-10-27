module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

public section

open Lean Elab Command Meta

namespace CFSG.KC.J4Q.Strs

meta def charsE (s : String) : Expr :=
  let charT := mkConst ``Char
  s.toList.foldr (fun ch acc => mkApp3 (mkConst ``List.cons [0]) charT
    (mkApp (mkConst ``Char.ofNat) (mkRawNatLit ch.toNat)) acc) (mkApp (mkConst ``List.nil [0]) charT)

meta partial def lits (e : Expr) : Array String :=
  match e with
  | .lit (.strVal s) => #[s]
  | .app f a => lits f ++ lits a
  | .lam _ t b _ => lits t ++ lits b
  | .forallE _ t b _ => lits t ++ lits b
  | .letE _ t v b _ => lits t ++ lits v ++ lits b
  | .mdata _ b => lits b
  | .proj _ _ b => lits b
  | _ => #[]

meta partial def subst (P : Name) (e : Expr) (i : Nat) : Expr × Nat :=
  match e with
  | .lit (.strVal _) => (mkApp (mkConst ``String.ofList) (mkConst (P ++ Name.mkSimple s!"s{i}")), i + 1)
  | .app f a =>
    let (f', i) := subst P f i
    let (a', i) := subst P a i
    (.app f' a', i)
  | .lam n t b bi =>
    let (t', i) := subst P t i
    let (b', i) := subst P b i
    (.lam n t' b' bi, i)
  | .forallE n t b bi =>
    let (t', i) := subst P t i
    let (b', i) := subst P b i
    (.forallE n t' b' bi, i)
  | .letE n t v b nd =>
    let (t', i) := subst P t i
    let (v', i) := subst P v i
    let (b', i) := subst P b i
    (.letE n t' v' b' nd, i)
  | .mdata m b =>
    let (b', i) := subst P b i
    (.mdata m b', i)
  | .proj s k b =>
    let (b', i) := subst P b i
    (.proj s k b', i)
  | e => (e, i)

meta def addStrs (P c : Name) : CoreM Unit := do
  let some (.defnInfo d) := (← getEnv).find? c | throwError "{c} is not a definition"
  let ss := lits d.value
  if ss.isEmpty then throwError "{c}: no string literal"
  let lc := mkApp (mkConst ``List [0]) (mkConst ``Char)
  for i in [0:ss.size] do
    addDecl (forceExpose := true) <| .defnDecl
      { name := P ++ Name.mkSimple s!"s{i}", levelParams := [], type := lc, value := charsE ss[i]!,
        hints := .regular 0, safety := .safe }
  let v := (subst P d.value 0).1
  let u ← Meta.MetaM.run' (Meta.getLevel d.type)
  let ty := mkApp3 (mkConst ``Eq [u]) d.type (mkConst c) v
  let pf := mkApp2 (mkConst ``Eq.refl [u]) d.type (mkConst c)
  CFSG.KC.addThmDecl <| { name := P ++ `eq, levelParams := [], type := ty, value := pf }

elab "#j4q_strs " P:ident c:ident : command =>
  liftCoreM <| withOptions (Elab.async.set · false) do
    let c ← realizeGlobalConstNoOverload c
    addStrs P.getId c

end CFSG.KC.J4Q.Strs
