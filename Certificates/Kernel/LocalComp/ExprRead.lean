module

public meta import Lean
public import Certificates.Data.CFSGNative.SectionRank.Local
public meta import Certificates.Data.CFSGNative.SectionRank.Local
public meta import Certificates.Data.CFSGNative.SectionRank.Elem3

open Lean Meta CFSG.SectionRank.Native

public section

namespace CFSG.KC.ExprRead

meta def natW (e : Expr) : MetaM Nat := do
  if let some n ← (evalNat (← instantiateMVars e)).run then return n
  let e' ← whnf e
  if let some n ← (evalNat e').run then return n
  throwError "ExprRead: not a natural number literal: {e}"

meta partial def listW (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    return e.appFn!.appArg! :: (← listW e.appArg!)
  else if e.isAppOfArity ``List.nil 1 then
    return []
  else
    throwError "ExprRead: not a list: {e}"

meta def opW (e : Expr) : MetaM Op := do
  let e ← whnf e
  if e.isAppOfArity ``Op.mul 3 then
    return .mul (← natW (e.getArg! 0)) (← natW (e.getArg! 1)) (← natW (e.getArg! 2))
  else if e.isAppOfArity ``Op.pow 3 then
    return .pow (← natW (e.getArg! 0)) (← natW (e.getArg! 1)) (← natW (e.getArg! 2))
  else
    throwError "ExprRead: not an operation: {e}"

meta def progW (e : Expr) : MetaM (List Op) := do
  (← listW e).mapM opW

meta structure SqV where
  nregs : Nat
  prog : List Op
  rx : Nat
  ry : Nat
  rh : Nat
  r : Nat
  oh : Nat
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  t : Nat

meta def sqW (D : Expr) : MetaM SqV := do
  let f (n : Name) : MetaM Nat := do natW (← mkAppM n #[D])
  return { nregs := ← f ``SqData.nregs, prog := ← progW (← mkAppM ``SqData.prog #[D]),
           rx := ← f ``SqData.rx, ry := ← f ``SqData.ry, rh := ← f ``SqData.rh, r := ← f ``SqData.r,
           oh := ← f ``SqData.oh, a := ← f ``SqData.a, b := ← f ``SqData.b, c := ← f ``SqData.c,
           d := ← f ``SqData.d, t := ← f ``SqData.t }

end CFSG.KC.ExprRead

end
