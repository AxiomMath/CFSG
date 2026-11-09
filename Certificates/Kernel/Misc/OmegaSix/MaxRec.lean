module

public meta import Certificates.Kernel.SporSch.HN.GenNTree
public import Certificates.Kernel.SporSch.HN.GenNTree
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

meta def CFSG.KD.OmegaSix.GenX.crRecs : List Nat :=
  (String.splitOn (include_str "MaxRec.0.txt") ",").map String.toNat!

meta def CFSG.KD.OmegaSix.GenX.hdrX : List Nat :=
  (String.splitOn (include_str "MaxRec.1.txt") ",").map String.toNat!

meta def CFSG.KD.OmegaSix.GenX.witX : List Nat :=
  (String.splitOn (include_str "MaxRec.2.txt") ",").map String.toNat!

#kss_ntree CFSG.KD.OmegaSix.RMC CFSG.KD.OmegaSix.GenX.crRecs
#kss_ntree CFSG.KD.OmegaSix.RMH CFSG.KD.OmegaSix.GenX.hdrX
#kss_ntree CFSG.KD.OmegaSix.RMW CFSG.KD.OmegaSix.GenX.witX
