module

public import Certificates.Kernel.GammaU.Triple0Data
public import Certificates.Kernel.GammaU.Triple1Data
public import CFSG.GF2Type.Smith1979.GammaU.ResidualPairInputs
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUT0 ct16966a (fun x => CFSG.KC.IF4C.allBelow 12 (CFSG.KD.GUT0.tri x)) 0 12
#kc_each CFSG.KD.GUT1 ct16966b (fun x => CFSG.KC.IF4C.allBelow 12 (CFSG.KD.GUT1.tri x)) 0 4

namespace CFSG.KD.GUT0

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU

#kc_forall_chunks ct16966a_all (fun x => allBelow 12 (tri x) = true) 12 CFSG.KD.GUT0.ct16966a 1

theorem ct16966a_cj : allBelow 12 cj = true := by decide +kernel

theorem ct16966a_lists : lists = true := by decide +kernel

theorem ct16966a_n2 : N2 = (ResPair.n2Gens 0).map CFSG.KC.IF4R.packR := by decide +kernel

theorem ct16966a_h10 : HM.map (subQ L) = (ResPair.hyp10 0).map CFSG.KC.IF4R.packR := by
  decide +kernel

theorem ct16966a_inv : invOK NLG NLGI 3 = true := by decide +kernel

end CFSG.KD.GUT0

namespace CFSG.KD.GUT1

open CFSG.KC.IF4C CFSG.KC.GUV CFSG.GF2Type.Smith1979.GammaU

#kc_forall_chunks ct16966b_all (fun x => allBelow 12 (tri x) = true) 4 CFSG.KD.GUT1.ct16966b 1

theorem ct16966b_cj : allBelow 12 cj = true := by decide +kernel

theorem ct16966b_lists : lists = true := by decide +kernel

theorem ct16966b_n2 : N2 = (ResPair.n2Gens 1).map CFSG.KC.IF4R.packR := by decide +kernel

theorem ct16966b_h10 : HM.map (subQ L) = (ResPair.hyp10 1).map CFSG.KC.IF4R.packR := by
  decide +kernel

theorem ct16966b_inv : invOK NLG NLGI 3 = true := by decide +kernel

end CFSG.KD.GUT1

end
