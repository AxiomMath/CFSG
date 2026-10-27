module

public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.UCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWData
public import CFSG.Certificates.Kernel.Common.Eval
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public meta import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CertificateChecks.KernelC24608

open CFSG.KC.Eval CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.AutETable
open CFSG.EvenSporadicStandard.Fin76b.UCheckAux

meta def uTabM (g : Nat) : Array (Array Nat) := if g == 0 then W16.eTab else W16.eTabJ3

public meta def stepU (vs : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let g : Nat := match vs[0]? with | some (Val.nat v) => v | _ => 0
  let T := uTabM g
  let tI := 21
  let m : Nat → Nat → Nat := fun a b => (T[a]!)[b]!
  let P := (List.range 1024).foldr (fun p acc => acc * 32 + m (p / 32) (p % 32)) 0
  let E := tab2 32 m
  let gw := mkGens 32 E
  let W := gw.2.map fun o => o.getD []
  let NU := tab2 256 (umul m tI)
  let mut ws : Array Val := #[]
  for p in List.range 256 do
    let i := p / 32
    let k := p % 32
    if peqB m tI (dMul i i, m k k) (0, 0) && !peqB m tI (i, k) (0, 0) &&
        !peqB m tI (i, k) (0, tI) then
      match usearch m tI E NU gw.1 W (i, k) with
      | some φ =>
        if !uVerify m tI (i, k) φ then throw s!"stepU: witness {p} fails"
        let x := (List.range 32).foldr (fun a acc =>
          acc * 256 + (32 * (φ.getD a (0, 0)).1 + (φ.getD a (0, 0)).2)) 0
        ws := ws.push (.nat x)
      | none => throw s!"stepU: no witness for {p}"
    else
      ws := ws.push (.nat 0)
  return #[(`P, .nat P), (`WS, .list ws)]

end CertificateChecks.KernelC24608

end
