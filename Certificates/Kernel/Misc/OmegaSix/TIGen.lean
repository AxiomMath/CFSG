module

public meta import Lean
meta import Certificates.Data.Foote82OmegaSixTI
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CFSG.KD.OmegaSix.GenTI

open CFSG.CGT.Foote82.OmegaSix CFSG.CGT.Foote82.InvolA6 CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def witOf (W : Enum) (t : Array Nat) : Nat := Id.run do
  let one := idA ()
  if compA t t != one || t == one || rank1 t then return 0
  for j in [0:W.elems.size] do
    let g := W.elems[j]!
    let k := (W.lookup (invArr g)).getD 0
    if k < W.elems.size && compA g W.elems[k]! == one && compA W.elems[k]! g == one then
      let gi := W.elems[k]!
      let u := compA (compA g t) gi
      let p := compA t u
      if compA p p == one then
        for c in [0:6] do
          let v := 2 ^ c
          if t[u[v]! ^^^ v]! != u[v]! ^^^ v then
            return j + 2 ^ 15 * k + 2 ^ 30 * c
  panic! "witOf: no witness"

meta def tiW : List Nat :=
  let O := oEnum ()
  let W := omegaEnum ()
  if O.elems.size != 51840 then panic! "tiW: |O| ≠ 51840" else
  (List.range 51840).map fun i => witOf W O.elems[i]!

meta def tiF : List Nat := [(tiW.findIdx? (· != 0)).getD 0]

end CFSG.KD.OmegaSix.GenTI

#kss_ntree CFSG.KD.OmegaSix.TIW CFSG.KD.OmegaSix.GenTI.tiW

#kss_ntree CFSG.KD.OmegaSix.TIF CFSG.KD.OmegaSix.GenTI.tiF
