module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import CFSG.Open.LocalVocabulary

namespace CFSG.KD.G24Id.Gen

meta def db : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def dc : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def dq1 : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def dq2 : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def dh1 : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

meta def dh2 : List Nat :=
  (String.splitOn (include_str "Rec.5.txt") ",").map String.toNat!

meta def de : List Nat :=
  (String.splitOn (include_str "Rec.6.txt") ",").map String.toNat!

end CFSG.KD.G24Id.Gen

#kss_ntree CFSG.KD.G24Id.DB CFSG.KD.G24Id.Gen.db

#kss_ntree CFSG.KD.G24Id.DC CFSG.KD.G24Id.Gen.dc
#kss_ntree CFSG.KD.G24Id.DQ1 CFSG.KD.G24Id.Gen.dq1
#kss_ntree CFSG.KD.G24Id.DQ2 CFSG.KD.G24Id.Gen.dq2
#kss_ntree CFSG.KD.G24Id.DH1 CFSG.KD.G24Id.Gen.dh1
#kss_ntree CFSG.KD.G24Id.DH2 CFSG.KD.G24Id.Gen.dh2
#kss_ntree CFSG.KD.G24Id.DE CFSG.KD.G24Id.Gen.de
