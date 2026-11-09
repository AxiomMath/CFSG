module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcFive.Census
public import Certificates.Kernel.MonsterPcFive.CensusData
public import Certificates.Kernel.MonsterPcFive.CensusSplit

public section

namespace CFSG.KC.MonPcFiveD

open CFSG.KC.MonPcFive

theorem m5Rep0a : repsRun rcs rep 916 0 5 rh0 rp0 = true := by quickRfl
theorem m5Rep0b : repsRun rcs rep 916 (0 + 5) 9 (skipH 5 rh0) (skipP 5 rh0 rp0) = true := by
  quickRfl
theorem m5Rep0c : repsRun rcs rep 916 (0 + (5 + 9)) 9 (skipH (5 + 9) rh0)
    (skipP (5 + 9) rh0 rp0) = true := by quickRfl
theorem m5Rep0d : repsRun rcs rep 916 (0 + (5 + 9 + 9)) 12 (skipH (5 + 9 + 9) rh0)
    (skipP (5 + 9 + 9) rh0 rp0) = true := by quickRfl
theorem m5Rep0 : repsRun rcs rep 916 0 35 rh0 rp0 = true :=
  repsRun_split _ _ 916 12 0 (5 + 9 + 9) rh0 rp0
    (repsRun_split _ _ 916 9 0 (5 + 9) rh0 rp0
      (repsRun_split _ _ 916 9 0 5 rh0 rp0 m5Rep0a m5Rep0b) m5Rep0c) m5Rep0d
theorem m5Rep1 : repsRun rcs rep 916 35 35 rh1 rp1 = true := by quickRfl
theorem m5Rep2 : repsRun rcs rep 916 70 35 rh2 rp2 = true := by quickRfl
theorem m5Rep3 : repsRun rcs rep 916 105 35 rh3 rp3 = true := by quickRfl
theorem m5Rep4 : repsRun rcs rep 916 140 35 rh4 rp4 = true := by quickRfl
theorem m5Rep5 : repsRun rcs rep 916 175 35 rh5 rp5 = true := by quickRfl
theorem m5Rep6 : repsRun rcs rep 916 210 35 rh6 rp6 = true := by quickRfl

end CFSG.KC.MonPcFiveD

end
