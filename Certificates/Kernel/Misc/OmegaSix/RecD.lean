module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenD

meta def recR : List Nat :=
  (String.splitOn (include_str "RecD.0.txt") ",").map String.toNat!

meta def recW : List Nat :=
  (String.splitOn (include_str "RecD.1.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenD

#kss_ntree CFSG.KD.OmegaSix.RCR CFSG.KD.OmegaSix.GenD.recR
#kss_ntree CFSG.KD.OmegaSix.RW CFSG.KD.OmegaSix.GenD.recW
