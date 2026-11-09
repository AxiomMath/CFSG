module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Assembly.LowTwoRankDefs

namespace CFSG.KD.G2Three.T1W.Gen

meta def rtV : List Nat :=
  (String.splitOn (include_str "T1Rec.0.txt") ",").map String.toNat!

meta def paV : List Nat :=
  (String.splitOn (include_str "T1Rec.1.txt") ",").map String.toNat!

meta def pbV : List Nat :=
  (String.splitOn (include_str "T1Rec.2.txt") ",").map String.toNat!

end CFSG.KD.G2Three.T1W.Gen

#kss_ntree CFSG.KD.G2Three.T1W.RT CFSG.KD.G2Three.T1W.Gen.rtV
#kss_ntree CFSG.KD.G2Three.T1W.PA CFSG.KD.G2Three.T1W.Gen.paV
#kss_ntree CFSG.KD.G2Three.T1W.PB CFSG.KD.G2Three.T1W.Gen.pbV
