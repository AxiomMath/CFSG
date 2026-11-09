module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenO

meta def recOO : List Nat :=
  (String.splitOn (include_str "RecO.0.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenO

#kss_ntree CFSG.KD.OmegaSix.ROO CFSG.KD.OmegaSix.GenO.recOO
