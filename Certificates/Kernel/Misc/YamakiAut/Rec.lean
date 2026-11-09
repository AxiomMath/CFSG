module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiAut.Gen

meta def recW : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def recQ : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

end CFSG.KD.YamakiAut.Gen

#kss_ntree CFSG.KD.YamakiAut.RW CFSG.KD.YamakiAut.Gen.recW
#kss_ntree CFSG.KD.YamakiAut.RQ CFSG.KD.YamakiAut.Gen.recQ
