module

public meta import Lean
meta import Certificates.Data.Sp62RecCR1CE
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiAut.Gen

open CFSG.KD.YamakiRep.Gen CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def enc (l : List Nat) : Nat := l.foldr (fun a acc => a + 16 * acc) 0

meta def compM (p q : List Nat) : List Nat := q.map fun j => p.getD j 0

meta def recImg (ws : List (List Nat)) (n : Nat) (sig : Array (List Nat)) : List Nat := Id.run do
  let (es, par, _, _) := bfsM (ws.map wordM).toArray n
  let mut P : Array (List Nat) := #[List.range (sig[0]!).length]
  for t in [1:es.size] do
    let (h, s) := par[t - 1]!
    P := P.push (compM P[h]! sig[s]!)
  return P.toList.map enc

meta def recW : List Nat :=
  recImg hWords 23040 #[[5, 8, 6, 7, 3, 10, 11, 2, 0, 1, 9, 4], [5, 4, 7, 3, 2, 6, 11, 10, 1, 9, 8, 0]]

meta def recQ : List Nat :=
  recImg nWords 10752 #[[8, 2, 12, 4, 3, 0, 6, 1, 9, 5, 11, 10, 7, 13],
    [2, 10, 1, 12, 7, 13, 4, 9, 3, 8, 5, 0, 6, 11]]

end CFSG.KD.YamakiAut.Gen

#kss_ntree CFSG.KD.YamakiAut.RW CFSG.KD.YamakiAut.Gen.recW
#kss_ntree CFSG.KD.YamakiAut.RQ CFSG.KD.YamakiAut.Gen.recQ
