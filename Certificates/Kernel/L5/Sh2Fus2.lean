module

public import Certificates.Data.Kernel.L5.Sh2FusT
public import Certificates.Data.Kernel.L5.Sh2EngD
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5.Sh2Fus

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD CFSG.KD.L5

variable
  (G : Group (Idx 256)) (hm : ∀ a b, mulI 2 a b = G.mul a b)
  (hi : ∀ a, invI 2 a = G.inv a) (ho : oneI = G.one)

theorem fus2 : @fusChkL 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho)
    (@fuseL 256 (grpOf G (mulI 2) hm (invI 2) hi oneI ho)
      (f5P eI (Sh2FusT.embT.map Prod.fst) Sh2FusT.f5C) (nbarPairsF embL))
    (embL x0T5) (engA 2).reps (engA 2).ciA (engA 2).invs (engA 2).x = true := by
  kc_decide_fv

end CFSG.KD.L5.Sh2Fus

end
