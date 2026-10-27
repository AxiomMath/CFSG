module

public import Certificates.Data.Kernel.Misc.G24
public import CFSG.LieType.Multipliers.G24Data
public import Certificates.Kernel.Misc.G24Data
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Certificates.CosetTablePresented
import all CFSG.Sporadic.Presentation.SuzInputs
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Suzuki
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator
public import CFSG.Certificates.CosetTableShort
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Sporadic.Presentation.Common

public section

set_option maxRecDepth 100000

namespace CFSG.KD.Misc.G24

open CFSG.KC.Misc.G24 CFSG.LieType.Multipliers.G24

theorem k44 : g24F4K GR Gb RS PS XS YS XL YL = true := by quickRfl
theorem k45 : g24F3K LR Lb Lib RS PS = true := by quickRfl
theorem suz : suzCheck = true := by quickRfl

end CFSG.KD.Misc.G24

end
