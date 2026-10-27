module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Mathlib.Data.ZMod.Defs
public meta import Certificates.Data.Foote82OmegaSixNorm
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

namespace CFSG.KD.OmegaSix.Trans

open CFSG.KC.Eval CFSG.CGT.Foote82.OmegaSix

public meta def stepT (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "stepT: expected no arguments"
  let E := omegaEnum ()
  let mut TW : Array Val := #[]
  for n in [0:64] do
    if q6 (cvec n) == 1 then
      match E.elems.findIdx? fun t => t[v0]! == n with
      | some j => TW := TW.push (.list #[.nat n, .nat j])
      | none => throw s!"stepT: no element maps v0 to {n}"
  return #[(`TW, .list TW)]

end CFSG.KD.OmegaSix.Trans
