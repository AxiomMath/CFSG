module

public meta import Lean
meta import Certificates.Data.YamakiAmalgam
meta import Certificates.Kernel.Misc.YamakiRep.Gen
public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.YamakiAutM.Gen

open CFSG.KD.YamakiRep.Gen CFSG.ClassicalInvolution.Solomon73.Yamaki

meta def recT : List Nat := Id.run do
  let (es, par, _, _) := bfsM (hWords.map wordM).toArray 23040
  let A : Array Nat := (tau1Words.map wordM).toArray
  let B : Array Nat := (tau2Words.map wordM).toArray
  let mut P : Array (Nat × Nat) := #[(oneM, oneM)]
  for t in [1:es.size] do
    let (h, s) := par[t - 1]!
    let (p, q) := P[h]!
    P := P.push (mulM p A[s]!, mulM q B[s]!)
  return P.toList.map fun (p, q) => p + 2 ^ 36 * q

end CFSG.KD.YamakiAutM.Gen

#kss_ntree CFSG.KD.YamakiAutM.RT CFSG.KD.YamakiAutM.Gen.recT
