module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.RankThree.PartTwo.Census.Carrier.Sp6TwoCodes

namespace CFSG.KD.Sp6A2.Gen

meta def recM : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

end CFSG.KD.Sp6A2.Gen

#kss_ntree CFSG.KD.Sp6A2.REC CFSG.KD.Sp6A2.Gen.recM
