
module

public import Certificates.Kernel.GammaU.SigmaFactsBase

public import Certificates.Kernel.GammaU.Sigma0OK
public import Certificates.Kernel.GammaU.Sigma1OK
public import CFSG.Certificates.Kernel.GammaUSigmaSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUS0

open CFSG.KC.IF4C CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem sigmaLvl0 :
    SigmaFacts 0 ∧ lvlGrp SP TL 0 = CFSG.GF2Type.Smith1979.GammaU.Viol.genGrp (pGens 0) :=
  sigmaFacts_of chainHyp0 (by decide +kernel) rfl rfl rfl rfl cs16981a_rows cs16981a_pairs
    cs16981a_inv cs16981a_sift cs16981a_rw cs16981a_dw cs16981a_stab cs16981a_reach
    cs16981a_sigma cs16981a_oval (by decide +kernel) cs16981a_nc

theorem sigmaFacts0 : SigmaFacts 0 := sigmaLvl0.1

end CFSG.KD.GUS0

namespace CFSG.KD.GUS1

open CFSG.KC.IF4C CFSG.KC.GUS CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem sigmaLvl1 :
    SigmaFacts 1 ∧ lvlGrp SP TL 0 = CFSG.GF2Type.Smith1979.GammaU.Viol.genGrp (pGens 1) :=
  sigmaFacts_of chainHyp1 (by decide +kernel) rfl rfl rfl rfl cs16981b_rows cs16981b_pairs
    cs16981b_inv cs16981b_sift cs16981b_rw cs16981b_dw cs16981b_stab cs16981b_reach
    cs16981b_sigma cs16981b_oval (by decide +kernel) cs16981b_nc

theorem sigmaFacts1 : SigmaFacts 1 := sigmaLvl1.1

end CFSG.KD.GUS1

namespace CFSG.KD.GUS

open CFSG.GF2Type.Smith1979.GammaU.SigmaP

theorem sigmaFacts : ∀ i, i = 0 ∨ i = 1 → SigmaFacts i := by
  rintro i (rfl | rfl)
  · exact CFSG.KD.GUS0.sigmaFacts0
  · exact CFSG.KD.GUS1.sigmaFacts1

end CFSG.KD.GUS

end
