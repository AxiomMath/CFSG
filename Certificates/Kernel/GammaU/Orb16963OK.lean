module

public import Certificates.Kernel.GammaU.Orb16963Data
public import CFSG.GF2Type.Smith1979.GammaU.StepAInputs
public import CFSG.GF2Type.Smith1979.GammaU.SigmaInputs
public import Certificates.Data.Kernel.GammaUSigmaK
public import Certificates.Data.Kernel.IdxFourSiftK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.GUO

open CFSG.KC.IF4C CFSG.KC.GUO CFSG.GF2Type.Smith1979.GammaU

theorem co16963_n0 : repOK SG R 0 N0 = true := by quickRfl

theorem co16963_n1 : repOK SG R 1 N1 = true := by quickRfl

theorem co16963_n2 : repOK SG R 2 N2 = true := by quickRfl

theorem co16963_n3 : repOK SG R 3 N3 = true := by quickRfl

theorem co16963_n4 : repOK SG R 4 N4 = true := by quickRfl

theorem co16963_n5 : repOK SG R 5 N5 = true := by quickRfl

theorem co16963_r0 : repF R 0 = true := by quickRfl

theorem co16963_r1 : repF R 1 = true := by quickRfl

theorem co16963_r2 : repF R 2 = true := by quickRfl

theorem co16963_r3 : repF R 3 = true := by quickRfl

theorem co16963_r4 : repF R 4 = true := by quickRfl

theorem co16963_r5 : repF R 5 = true := by quickRfl

theorem co16963_tree : treeOK GG SM TR = true := by quickRfl

theorem co16963_sm : smOK SM = true := by quickRfl

theorem co16963_gens : gensOK TH SG GG = true := by quickRfl

theorem co16963_pin : TH = CFSG.KC.IF4R.packR SigmaP.thetaRows ∧
    SG = StepA.saGens.map CFSG.KC.IF4R.packR ∧ GG = StepA.gamuGens.map CFSG.KC.IF4R.packR ∧
    R = StepA.dReps ∧ CFSG.KC.GUS.rowsOK SigmaP.thetaRows.toList = true ∧
    (StepA.saGens.all fun r => CFSG.KC.GUS.rowsOK r.toList) = true ∧
    (StepA.gamuGens.all fun r => CFSG.KC.GUS.rowsOK r.toList) = true := by
  decide +kernel

end CFSG.KD.GUO

end
