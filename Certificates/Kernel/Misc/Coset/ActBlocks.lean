module

public import CFSG.Certificates.Kernel.Misc.Coset.ActSound
public meta import Lean
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.KC.MiscCoset.Act

open Lean Meta Elab Tactic

meta def numLit (e : Expr) : MetaM Nat := do
  if let some v := e.rawNatLit? then return v
  if let some v := e.nat? then return v
  throwError "not a numeral:{indentExpr e}"

meta def allRParts (t : Expr) : MetaM (Nat × Nat × Expr) := do
  let some (_, lhs, _) := t.eq? | throwError "not an equation `allR lo n p = true`:{indentExpr t}"
  unless lhs.isAppOfArity ``allR 3 do throwError "not an `allR lo n p`:{indentExpr lhs}"
  let args := lhs.getAppArgs
  return (← numLit args[0]!, ← numLit args[1]!, args[2]!)

meta def allRStmt (lo n : Nat) (p : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
    (mkApp3 (mkConst ``allR) (mkRawNatLit lo) (mkRawNatLit n) p) (mkConst ``Bool.true)

meta def allRChain (lo : Nat) (p : Expr) (parts : Array (Nat × Nat × Expr)) : MetaM Expr := do
  let some (s0, a0, h0) := parts[0]? | throwError "allR: no parts"
  unless s0 == lo do throwError "allR: the first part starts at {s0}, not {lo}"
  let mut a := a0
  let mut acc := h0
  for (c, b, h) in parts[1:] do
    unless c == lo + a do throwError "allR: a part starts at {c}, expected {lo + a}"
    acc := mkAppN (mkConst ``allR_join')
      #[mkRawNatLit lo, mkRawNatLit a, mkRawNatLit c, mkRawNatLit b, mkRawNatLit (a + b), p, acc, h,
        reflBoolTrue, reflBoolTrue]
    a := a + b
  return acc

elab "allR_blocks " bN:num : tactic => liftMetaFinishingTactic fun g => do
  let (lo, n, p) ← allRParts (← instantiateMVars (← g.getType))
  let B := bN.getNat
  unless 0 < B ∧ 0 < n do throwError "allR_blocks: empty block or range"
  let mut parts := #[]
  for k in [0:(n + B - 1) / B] do
    let s := lo + B * k
    let b := min B (lo + n - s)
    let nm ← mkAuxLemma [] (allRStmt s b p) reflBoolTrue (kind? := `blk) (cache := false)
    parts := parts.push (s, b, mkConst nm)
  g.assign (← allRChain lo p parts)

end CFSG.KC.MiscCoset.Act

end
