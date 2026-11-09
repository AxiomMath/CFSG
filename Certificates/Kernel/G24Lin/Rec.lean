module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Open.LocalVocabulary

namespace CFSG.KD.G24Lin.Gen

meta def dq1 : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def dq2 : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def dc : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def de : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def cq1 : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

meta def cq2 : List Nat :=
  (String.splitOn (include_str "Rec.5.txt") ",").map String.toNat!

end CFSG.KD.G24Lin.Gen

#kss_ntree CFSG.KD.G24Lin.DQ1 CFSG.KD.G24Lin.Gen.dq1
#kss_ntree CFSG.KD.G24Lin.DQ2 CFSG.KD.G24Lin.Gen.dq2
#kss_ntree CFSG.KD.G24Lin.DC CFSG.KD.G24Lin.Gen.dc
#kss_ntree CFSG.KD.G24Lin.DE CFSG.KD.G24Lin.Gen.de
#kss_ntree CFSG.KD.G24Lin.CQ1 CFSG.KD.G24Lin.Gen.cq1
#kss_ntree CFSG.KD.G24Lin.CQ2 CFSG.KD.G24Lin.Gen.cq2
