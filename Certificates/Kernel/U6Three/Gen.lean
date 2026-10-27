module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.Kernel.U6Three.Defs
public meta import Certificates.Data.U6ThreeRank
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

namespace CFSG.KC.U6Three

open CFSG.KC.Eval

open CFSG.RankThree.PartOne.F106

public meta def stepU6 (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let mut tp := 0
  let mut jp := 0
  let mut i := 0
  for w in u6ThreePaths do
    let c := w.foldl (fun a k => mulN a (genC k)) 0
    tp := tp ||| (c <<< (13 * i))
    jp := jp ||| (i <<< (10 * c))
    i := i + 1
  let mut ip := 0
  let mut j := 0
  for v in u6ThreeInv do
    ip := ip ||| (v <<< (10 * j))
    j := j + 1
  return #[(`TP, .nat tp), (`IP, .nat ip), (`JP, .nat jp)]

end CFSG.KC.U6Three
