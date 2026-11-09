module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiA6.Gen

meta def recP : List Nat :=
  (String.splitOn (include_str "RecA6.0.txt") ",").map String.toNat!

end CFSG.KD.YamakiA6.Gen

#kss_ntree CFSG.KD.YamakiA6.RP CFSG.KD.YamakiA6.Gen.recP
