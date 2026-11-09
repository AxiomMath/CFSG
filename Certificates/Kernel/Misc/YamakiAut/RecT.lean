module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.YamakiAutM.Gen

meta def recT : List Nat :=
  (String.splitOn (include_str "RecT.0.txt") ",").map String.toNat!

end CFSG.KD.YamakiAutM.Gen

#kss_ntree CFSG.KD.YamakiAutM.RT CFSG.KD.YamakiAutM.Gen.recT
