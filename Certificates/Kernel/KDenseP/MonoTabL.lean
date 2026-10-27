module

public import Certificates.Kernel.KDenseP.Axis.Base

public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP

open Lean Meta Elab Tactic in
elab "kd_monoTabL " pre:ident base:ident : tactic => liftMetaFinishingTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "kd_monoTabL: the goal is not an equation"
  let_expr monoTabOK F MT := lhs | throwError "kd_monoTabL: the goal is not monoTabOK F MT = true"
  let some v := (← getConstInfo MT.constName!).value?
    | throwError "kd_monoTabL: {MT} has no value"
  let mut L := v.appFn!.appArg!
  if L.isConst then
    let some lv := (← getConstInfo L.constName!).value?
      | throwError "kd_monoTabL: {L} has no value"
    L := lv
  let mut elems : Array Expr := #[]
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    L := L.headBeta
    if let .mdata _ e := L then
      L := e
    else if L.isAppOfArity ``List.cons 3 then
      elems := elems.push L.appFn!.appArg!
      L := L.appArg!
    else
      break
  unless L.isAppOfArity ``List.nil 1 do throwError "kd_monoTabL: the keys are not a literal list"
  let n := elems.size
  let cons := mkApp (mkConst ``List.cons [Level.zero]) L.appArg!
  let mut tails : Array Expr := Array.replicate (n + 1) L
  for i in [0:n] do
    let k := n - 1 - i
    tails := tails.set! k (mkApp2 cons elems[k]! tails[k + 1]!)
  let mut prf := mkApp3 (mkConst ``monoFold_nil) F MT (mkRawNatLit n)
  for i in [0:n] do
    let k := n - 1 - i
    let tk := mkConst (pre.getId ++ Name.mkSimple s!"{base.getId}{k}")
    prf := mkAppN (mkConst ``monoFold_cons) #[F, MT, elems[k]!, tails[k + 1]!, mkRawNatLit k, tk, prf]
  g.assign (mkApp3 (mkConst ``monoTabOK_of_fold) F MT prf)

end CertificateChecks.KernelKDenseP.Axis

end
