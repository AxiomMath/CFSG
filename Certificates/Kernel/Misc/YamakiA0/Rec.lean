module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CFSG.KD.YamakiA0.Gen

meta def recM : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

end CFSG.KD.YamakiA0.Gen

#kss_ntree CFSG.KD.YamakiA0.REC CFSG.KD.YamakiA0.Gen.recM
