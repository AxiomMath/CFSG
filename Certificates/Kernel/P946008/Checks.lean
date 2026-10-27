module

public import Certificates.Data.Kernel.P946008.Defs

public section

namespace CFSG.KC.P946008

open CFSG.RankThree.GF2n.Parrott

theorem ch946008m1a : Ms1H * Ms1HInv = 1 := by decide +kernel
theorem ch946008m1b : Ms1HInv * Ms1H = 1 := by decide +kernel
theorem ch946008m1c : Ms1H * Ms1H * Ms1H = 1 := by decide +kernel
theorem ch946008m2a : Ms2H * Ms2HInv = 1 := by decide +kernel
theorem ch946008m2b : Ms2HInv * Ms2H = 1 := by decide +kernel
theorem ch946008m2c : Ms2H * Ms2H * Ms2H = 1 := by decide +kernel
theorem ch946008m3a : Ms1s2H * Ms1s2HInv = 1 := by decide +kernel
theorem ch946008m3b : Ms1s2HInv * Ms1s2H = 1 := by decide +kernel
theorem ch946008m3c : Ms1s2H * Ms1s2H * Ms1s2H = 1 := by decide +kernel
theorem ch946008m4a : Ms1s2invH * Ms1s2invHInv = 1 := by decide +kernel
theorem ch946008m4b : Ms1s2invHInv * Ms1s2invH = 1 := by decide +kernel
theorem ch946008m4c : Ms1s2invH * Ms1s2invH * Ms1s2invH = 1 := by decide +kernel

theorem ch946008s1 :
    (liftK (packT (bitRow Ms1H) 256) (packT (cMask cMs1) 256) 8 2 true &&
      ord4G (phiK (packT (bitRow Ms1H) 256) (packT (cMask cMs1) 256))) = true := by
  decide +kernel

theorem ch946008s2 :
    (liftK (packT (bitRow Ms2H) 256) (packT (cMask cMs2) 256) 8 2 true &&
      ord4G (phiK (packT (bitRow Ms2H) 256) (packT (cMask cMs2) 256))) = true := by
  decide +kernel

theorem ch946008s3 :
    (liftK (packT (bitRow Ms1s2H) 256) (packT (cMask cMs1s2) 256) 2 2 false &&
      centralG (phiK (packT (bitRow Ms1s2H) 256) (packT (cMask cMs1s2) 256))) = true := by
  decide +kernel

theorem ch946008s4 :
    (liftK (packT (bitRow Ms1s2invH) 256) (packT (cMask cMs1s2inv) 256) 32 20 true &&
      (invCountG (phiK (packT (bitRow Ms1s2invH) 256) (packT (cMask cMs1s2inv) 256)) == 20) &&
      (centreG (phiK (packT (bitRow Ms1s2invH) 256) (packT (cMask cMs1s2inv) 256)) == 2) &&
      ord4G (phiK (packT (bitRow Ms1s2invH) 256) (packT (cMask cMs1s2inv) 256))) = true := by
  decide +kernel

end CFSG.KC.P946008
