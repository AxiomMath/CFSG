module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import Certificates.Data.F4ThreeRank

namespace CFSG.KC.F4Three

open CFSG.KC.Eval CFSG.RankThree.PartOne.F106

public meta def stepF4 (_ : Array Val) : Except String (Array (Lean.Name × Val)) := do
  let gb := f4ThreeCert.gbList
  let t := (f4ThreeCert.tabList gb).toArray
  let mut rows : Array Val := #[]
  for r in [0:27] do
    rows := rows.push (.list ((t.extract (27 * r) (27 * r + 27)).map Val.nat))
  return #[(`GB, .list (gb.toArray.map Val.nat)), (`TT, .list rows)]

end CFSG.KC.F4Three
