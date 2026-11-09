module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenC

meta def recA : List Nat :=
  (String.splitOn (include_str "RecC.0.txt") ",").map String.toNat!

meta def recB : List Nat :=
  (String.splitOn (include_str "RecC.1.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenC

#kss_ntree CFSG.KD.OmegaSix.RCA CFSG.KD.OmegaSix.GenC.recA
#kss_ntree CFSG.KD.OmegaSix.RCB CFSG.KD.OmegaSix.GenC.recB
