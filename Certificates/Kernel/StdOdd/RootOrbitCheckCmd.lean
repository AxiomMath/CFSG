module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm
public meta import CFSG.Certificates.Kernel.Common.Tab
public import Certificates.Data.Kernel.StdOdd.RootOrbit
public import CFSG.Certificates.Kernel.Common.AddThm
public import CFSG.Certificates.Kernel.Common.Tab
public import Lean.Exception

public section

namespace CFSG.KC.StdOdd.Orbit

open Lean Elab Command CFSG.KC.Tab

theorem forall_lt_zero (P : Nat → Prop) : ∀ t < 0, P t := fun _ h => absurd h (Nat.not_lt_zero _)

theorem forall_lt_succ (P : Nat → Prop) (n : Nat) (h : ∀ t < n, P t) (hn : P n) :
    ∀ t < n + 1, P t := by
  intro t ht
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
  · exact h t ht
  · exact hn

meta def ofNatE (k : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [0]) natT (lit k) (mkApp (mkConst ``instOfNatNat) (lit k))

meta def ltE (x y : Expr) : Expr := mkApp4 (mkConst ``LT.lt [0]) natT (mkConst ``instLTNat) x y

meta def isTrueE (b : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``Bool.true)

meta def addRange (name : Name) (stmt : Expr → Expr) (n : Nat) (bound : Expr) : CoreM Unit := do
  let motive := mkLambda `k .default natT (stmt (mkBVar 0))
  let mut pf := mkApp (mkConst ``forall_lt_zero) motive
  for k in [0:n] do
    let nm := name.appendAfter s!"{k}"
    CFSG.KC.addThmDecl <|
      { name := nm, levelParams := [], type := stmt (lit k), value := reflBoolTrue }
    pf := mkApp4 (mkConst ``forall_lt_succ) motive (lit k) pf (mkConst nm)
  let ty := mkForall `k .default natT
    (mkForall `h .default (ltE (mkBVar 0) bound) (stmt (mkBVar 1)))
  CFSG.KC.addThmDecl <| { name, levelParams := [], type := ty, value := pf }

elab "#e6_orbit_checks " pre:ident a:ident b:ident : command => do
  let P := (← getCurrNamespace) ++ pre.getId
  let aN ← liftCoreM <| realizeGlobalConstNoOverload a
  let bN ← liftCoreM <| realizeGlobalConstNoOverload b
  let some D := ((← getEnv).find? (P ++ `D)).bind (·.value?) |>.bind (·.rawNatLit?)
    | throwError "#e6_orbit_checks: {P ++ `D} is not a literal definition"
  let c := fun (s : Name) => mkConst (P ++ s)
  let close (M N : Expr) (k : Expr) : Expr :=
    isTrueE (mkAppN (mkConst ``closeOK) #[c `DS, M, N, c `PL, k])
  let succE (k : Expr) : Expr :=
    mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) natT natT natT
      (mkApp2 (mkConst ``instHAdd [0]) natT (mkConst ``instAddNat)) k (ofNatE 1)
  let step (k : Expr) : Expr :=
    isTrueE (mkApp2 (mkConst ``Nat.beq)
      (mkAppN (mkConst ``stepN) #[c `DS, c `MA, c `DS, c `MB, mkApp2 (mkConst ``nthN) (c `RS) k])
      (mkApp2 (mkConst ``nthN) (c `RS) (succE k)))
  withSync do
    addRange (P ++ `cA) (close (c `MA) (mkConst aN)) 156 (ofNatE 156)
    addRange (P ++ `cB) (close (c `MB) (mkConst bN)) 156 (ofNatE 156)
    addRange (P ++ `s) step D (c `D)

end CFSG.KC.StdOdd.Orbit

end
