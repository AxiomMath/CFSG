module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.GenF

meta def recRF : List Nat :=
  (String.splitOn (include_str "RecF.0.txt") ",").map String.toNat!

meta def recPW : List Nat :=
  (String.splitOn (include_str "RecF.1.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenF

#kss_ntree CFSG.KD.OmegaSix.RCF CFSG.KD.OmegaSix.GenF.recRF
#kss_ntree CFSG.KD.OmegaSix.PWF CFSG.KD.OmegaSix.GenF.recPW
