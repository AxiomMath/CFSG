module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiA6.GenV

meta def posVE : List Nat :=
  (String.splitOn (include_str "RecA6V.0.txt") ",").map String.toNat!

end CFSG.KD.YamakiA6.GenV

#kss_ntree CFSG.KD.YamakiA6.PVE CFSG.KD.YamakiA6.GenV.posVE
