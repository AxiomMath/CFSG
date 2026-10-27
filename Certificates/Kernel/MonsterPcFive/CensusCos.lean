module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcFive.Census
public import Certificates.Kernel.MonsterPcFive.CensusData

public section

namespace CFSG.KC.MonPcFiveD

open CFSG.KC.MonPcFive

theorem m5A : aOK nrm = true := by quickRfl

theorem m5Cos0 : cosRun rcs 0 cs0 = true := by quickRfl
theorem m5Cos1 : cosRun rcs 625 cs1 = true := by quickRfl
theorem m5Cos2 : cosRun rcs 1250 cs2 = true := by quickRfl
theorem m5Cos3 : cosRun rcs 1875 cs3 = true := by quickRfl
theorem m5Cos4 : cosRun rcs 2500 cs4 = true := by quickRfl

theorem m5CosLen : cs0.length = 625 ∧ cs1.length = 625 ∧ cs2.length = 625 ∧ cs3.length = 625 ∧
    cs4.length = 625 ∧ rcs.length = 245 := by decide +kernel

end CFSG.KC.MonPcFiveD

end
