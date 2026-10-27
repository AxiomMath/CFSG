module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Cocode24Check
public import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Rat.Cast.Order
public meta import Mathlib.GroupTheory.Perm.Basic
public meta import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CertificateChecks.KernelCocode

open CFSG.KC.Eval CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

public meta def packW (w : Nat) (l : List Nat) : Nat :=
  l.foldr (fun x acc => x + acc * 2 ^ w) 0

public meta def natL (xs : List Nat) : Val := .list (xs.toArray.map Val.nat)

public meta def stepCocode (_ : Array Val) : Except String (Array (Lean.Name × Val)) :=
  let tabs := tabsArr sylowTabs
  let rows := rowsOf tabs
  let row (i : Nat) : List Nat :=
    let r := rows.getD i #[]
    (List.range 1024).map fun j => r.getD j 0
  let blk (b : Nat) : Nat := packW 10 ((List.range 32).flatMap fun r => row (32 * b + r))
  let L := tabs.toList
  let pos (t : List Nat) : Nat := L.idxOf t
  let cl : List Nat := L.flatMap fun l => sylowTabs.map fun g => pos (tmul l g)
  .ok #[(`LT, .list (L.toArray.map natL)),
    (`KT, natL (L.map (packW 5))),
    (`EP, .nat (packW 120 (L.map (packW 5)))),
    (`RB, natL ((List.range 32).map blk)),
    (`CB, .nat (packW 10 cl)),
    (`IV, natL ((List.range 1024).filter fun i => isInv (L.getD i [])))]

end CertificateChecks.KernelCocode

end
