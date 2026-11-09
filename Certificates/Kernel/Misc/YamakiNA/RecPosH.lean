module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen

namespace CFSG.KD.YamakiNA.GenH

meta def posHX : List Nat :=
  (String.splitOn (include_str "RecPosH.0.txt") ",").map String.toNat!

end CFSG.KD.YamakiNA.GenH

#kss_ntree CFSG.KD.YamakiNA.PHX CFSG.KD.YamakiNA.GenH.posHX
