module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.AddThm
public meta import Certificates.Kernel.J4Q.AllN
public import Certificates.Kernel.J4Q.AllN

public section

namespace CFSG.KC.J4Q

open Lean Elab Command

meta def addAllSplit (P f fA fB lem : Name) (n : Nat) : CoreM Unit := do
  let boolT := mkConst ``Bool
  let natT := mkConst ``Nat
  let isT (e : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) boolT e (mkConst ``Bool.true)
  for k in [0:n] do
    let a := P ++ Name.mkSimple s!"a{k}"
    let b := P ++ Name.mkSimple s!"b{k}"
    let ta := isT (mkApp (mkConst fA) (mkRawNatLit k))
    let tb := isT (mkApp (mkConst fB) (mkRawNatLit k))
    let tt := isT (mkApp (mkConst f) (mkRawNatLit k))
    let vt := mkApp3 (mkConst lem) (mkRawNatLit k) (mkConst a) (mkConst b)
    CFSG.KC.addThmDecl { name := a, levelParams := [], type := ta, value := Lean.reflBoolTrue }
    CFSG.KC.addThmDecl { name := b, levelParams := [], type := tb, value := Lean.reflBoolTrue }
    CFSG.KC.addThmDecl { name := P ++ Name.mkSimple s!"t{k}", levelParams := [], type := tt, value := vt }
  let pred := mkLambda `t .default natT (isT (mkApp (mkConst f) (mkBVar 0)))
  let mut pf := mkApp (mkConst ``forall_lt_zero') pred
  for k in [0:n] do
    pf := mkAppN (mkConst ``forall_lt_succ') #[pred, mkRawNatLit k, pf, mkConst (P ++ Name.mkSimple s!"t{k}")]
  let ty := mkForall `t .default natT (mkForall `h .default
    (mkAppN (mkConst ``LT.lt [0]) #[natT, mkConst ``instLTNat, mkBVar 0, mkRawNatLit n])
    (isT (mkApp (mkConst f) (mkBVar 1))))
  CFSG.KC.addThmDecl <| { name := P ++ `all, levelParams := [], type := ty, value := pf }

elab "#j4m2_split " P:ident f:ident fA:ident fB:ident lem:ident n:num : command =>
  liftCoreM <| withOptions (Elab.async.set · false) do
    let f ← realizeGlobalConstNoOverload f
    let fA ← realizeGlobalConstNoOverload fA
    let fB ← realizeGlobalConstNoOverload fB
    let lem ← realizeGlobalConstNoOverload lem
    addAllSplit P.getId f fA fB lem n.getNat

end CFSG.KC.J4Q

end
