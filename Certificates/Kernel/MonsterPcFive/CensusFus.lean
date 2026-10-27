module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcFive.Census
public import Certificates.Kernel.MonsterPcFive.CensusData

public section

namespace CFSG.KC.MonPcFiveD

open CFSG.KC.MonPcFive

theorem m5Fus0 : fusW rep depth kind arg cls wit 916 0 229 = true := by quickRfl
theorem m5Fus1 : fusW rep depth kind arg cls wit 916 229 229 = true := by quickRfl
theorem m5Fus2 : fusW rep depth kind arg cls wit 916 458 229 = true := by quickRfl
theorem m5Fus3 : fusW rep depth kind arg cls wit 916 687 229 = true := by quickRfl

end CFSG.KC.MonPcFiveD

end
