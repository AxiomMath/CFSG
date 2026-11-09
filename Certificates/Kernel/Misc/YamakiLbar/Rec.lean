module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CFSG.KD.YamakiLbar.Gen

meta def qM : List Nat :=
  (String.splitOn (include_str "Rec.0.txt") ",").map String.toNat!

meta def wM : List Nat :=
  (String.splitOn (include_str "Rec.1.txt") ",").map String.toNat!

end CFSG.KD.YamakiLbar.Gen

#kss_ntree CFSG.KD.YamakiLbar.QREC CFSG.KD.YamakiLbar.Gen.qM
#kss_ntree CFSG.KD.YamakiLbar.WREC CFSG.KD.YamakiLbar.Gen.wM
