module

public import Certificates.Kernel.OmegaEight.Forms
public import Certificates.Kernel.OmegaEight.OrthGens
public import Certificates.Data.Kernel.O8.Orth
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitConeData
public import Mathlib

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Stage1

theorem kFormP : formOK QP = true := by quickRfl
theorem kFormM : formOK QM = true := by quickRfl
theorem kGenP : genOK QP GPlus GIPlus = true := by quickRfl
theorem kGenM : genOK QM GMinus GIMinus = true := by quickRfl
theorem kOrbP : orbitOK QP GPlus 12 (orbitWords .plus).toList = true := by quickRfl
theorem kOrbM : orbitOK QM GMinus 4 (orbitWords .minus).toList = true := by quickRfl
theorem kDickP : genDickOK GPlus GIPlus = true := by quickRfl
theorem kDickM : genDickOK GMinus GIMinus = true := by quickRfl
theorem kConeP : coneOK QP CXP CXiP CYP CYiP CCP = true := by quickRfl
theorem kConeM : coneOK QM CXM CXiM CYM CYiM CCM = true := by quickRfl

end CertificateChecks.KernelO8

end
