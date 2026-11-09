module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Certificates.Kernel.Misc.YamakiRep.Gen
import Mathlib.Tactic.NormNum.Ineq

namespace CFSG.KD.YamakiRep.Gen

meta def recX : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def recN : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

meta def recH : List Nat :=
  (String.splitOn (include_str "Rec.2.txt") ",").map String.toNat!

meta def recE : List Nat :=
  (String.splitOn (include_str "Rec.3.txt") ",").map String.toNat!

meta def recV : List Nat :=
  (String.splitOn (include_str "Rec.4.txt") ",").map String.toNat!

end CFSG.KD.YamakiRep.Gen

#kss_ntree CFSG.KD.YamakiRep.RX CFSG.KD.YamakiRep.Gen.recX
#kss_ntree CFSG.KD.YamakiRep.RN CFSG.KD.YamakiRep.Gen.recN
#kss_ntree CFSG.KD.YamakiRep.RH CFSG.KD.YamakiRep.Gen.recH
#kss_ntree CFSG.KD.YamakiRep.RE CFSG.KD.YamakiRep.Gen.recE
#kss_ntree CFSG.KD.YamakiRep.RV CFSG.KD.YamakiRep.Gen.recV
