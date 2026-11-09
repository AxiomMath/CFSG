module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.OmegaSix.Gen

meta def recO : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def posO : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.Gen

#kss_ntree CFSG.KD.OmegaSix.RO CFSG.KD.OmegaSix.Gen.recO
#kss_ntree CFSG.KD.OmegaSix.ROP CFSG.KD.OmegaSix.Gen.posO
