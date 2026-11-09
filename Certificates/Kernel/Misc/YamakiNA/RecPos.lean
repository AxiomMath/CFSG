module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.YamakiNA.Gen

meta def posNX : List Nat :=
  (String.splitOn (include_str "RecPos.0.txt") ",").map String.toNat!

end CFSG.KD.YamakiNA.Gen

#kss_ntree CFSG.KD.YamakiNA.PNX CFSG.KD.YamakiNA.Gen.posNX
