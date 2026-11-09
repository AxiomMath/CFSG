module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Data.FunLike.Basic

namespace CFSG.KD.SylowG2.Gen

meta def recPS : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def recQS : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def hqS : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def recTS : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def recUS : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

end CFSG.KD.SylowG2.Gen

#kss_ntree CFSG.KD.SylowG2.RPP CFSG.KD.SylowG2.Gen.recPS
#kss_ntree CFSG.KD.SylowG2.RQQ CFSG.KD.SylowG2.Gen.recQS
#kss_ntree CFSG.KD.SylowG2.HQ CFSG.KD.SylowG2.Gen.hqS
#kss_ntree CFSG.KD.SylowG2.RT CFSG.KD.SylowG2.Gen.recTS
#kss_ntree CFSG.KD.SylowG2.RU CFSG.KD.SylowG2.Gen.recUS
