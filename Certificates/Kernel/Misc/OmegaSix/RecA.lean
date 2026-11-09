module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenA

meta def recRA : List Nat :=
  (String.splitOn (include_str "RecA.0.txt") ",").map String.toNat!

meta def recRB : List Nat :=
  (String.splitOn (include_str "RecA.1.txt") ",").map String.toNat!

meta def recL : List Nat :=
  (String.splitOn (include_str "RecA.2.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenA

#kss_ntree CFSG.KD.OmegaSix.RCA3 CFSG.KD.OmegaSix.GenA.recRA
#kss_ntree CFSG.KD.OmegaSix.RCB3 CFSG.KD.OmegaSix.GenA.recRB
#kss_ntree CFSG.KD.OmegaSix.RL CFSG.KD.OmegaSix.GenA.recL
