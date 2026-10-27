module

public import Certificates.Kernel.HN1408.W441872Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441872

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KD.HN1408 CFSG.KD.HN1408.Y442202
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel

theorem ch441872_rec : recOK SW.G SW.GI SW.k SW.cnt SW.T SW.PL SW.POS SW.SRT SW.SRI = true := by
  quickRfl

theorem ch441872_cnt : SW.cnt = 256 := rfl

theorem ch441872_k : SW.k = 5 := rfl

theorem ch441872_gens : gensK SW.G witSylow (nat_lit 5) = true := by quickRfl

theorem ch441872_cent : centK SW.G = true := by quickRfl

theorem ch441872_inv : gensInvK = true := by quickRfl

theorem ch441872_vt : vtK V = true := by quickRfl

theorem ch441872_vert : vertsK V vMode vSq = true := by quickRfl

theorem ch441872_cov : covK SW.T (r32 CV) V = true := by quickRfl

end CFSG.KD.HN1408.W441872

end
