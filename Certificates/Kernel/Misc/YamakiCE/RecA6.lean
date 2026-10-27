module

public meta import Lean
meta import Certificates.Data.Sp62RecCR1CE
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiA6.Gen

open CFSG.KD.YamakiRep.Gen CFSG.ClassicalInvolution.Sp62Rec

meta def enc (l : List Nat) : Nat := l.foldr (fun a acc => a + 8 * acc) 0

meta def compM (p q : List Nat) : List Nat := q.map fun j => p.getD j 0

meta def recP : List Nat := Id.run do
  let (es, par, _, _) := bfsM (e0Words.map wordM).toArray 11520
  let sig : Array (List Nat) := #[[5, 3, 1, 2, 0, 4], [5, 1, 2, 0, 4, 3]]
  let mut P : Array (List Nat) := #[[0, 1, 2, 3, 4, 5]]
  for t in [1:es.size] do
    let (h, s) := par[t - 1]!
    P := P.push (compM P[h]! sig[s]!)
  return P.toList.map enc

end CFSG.KD.YamakiA6.Gen

#kss_ntree CFSG.KD.YamakiA6.RP CFSG.KD.YamakiA6.Gen.recP
