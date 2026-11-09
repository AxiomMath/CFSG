module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

namespace CFSG.KD.OmegaSix.GenTI

meta def tiW : List Nat :=
  (String.splitOn (include_str "TIGen.0.txt") ",").map String.toNat!

meta def tiF : List Nat :=
  (String.splitOn (include_str "TIGen.1.txt") ",").map String.toNat!

end CFSG.KD.OmegaSix.GenTI

#kss_ntree CFSG.KD.OmegaSix.TIW CFSG.KD.OmegaSix.GenTI.tiW

#kss_ntree CFSG.KD.OmegaSix.TIF CFSG.KD.OmegaSix.GenTI.tiF
