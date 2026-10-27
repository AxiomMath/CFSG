module

public import Certificates.Kernel.Sporadic.OddCore.HL
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt

theorem oE0_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 0)
    (offF HOF.T (HOF.TO 0)) (offF HOF.PL (HOF.PLO 0)) (offF HOF.POS (HOF.POSO 0))
    (offF HOF.SRT (HOF.SRTO 0)) (offF HOF.SRI (HOF.SRIO 0)) 0 450 = true := by quickRfl
theorem oE1_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 1)
    (offF HOF.T (HOF.TO 1)) (offF HOF.PL (HOF.PLO 1)) (offF HOF.POS (HOF.POSO 1))
    (offF HOF.SRT (HOF.SRTO 1)) (offF HOF.SRI (HOF.SRIO 1)) 0 450 = true := by quickRfl
theorem oE2_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 2)
    (offF HOF.T (HOF.TO 2)) (offF HOF.PL (HOF.PLO 2)) (offF HOF.POS (HOF.POSO 2))
    (offF HOF.SRT (HOF.SRTO 2)) (offF HOF.SRI (HOF.SRIO 2)) 0 450 = true := by quickRfl
theorem oE2_1 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 2)
    (offF HOF.T (HOF.TO 2)) (offF HOF.PL (HOF.PLO 2)) (offF HOF.POS (HOF.POSO 2))
    (offF HOF.SRT (HOF.SRTO 2)) (offF HOF.SRI (HOF.SRIO 2)) 450 450 = true := by quickRfl
theorem oE2_2 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 2)
    (offF HOF.T (HOF.TO 2)) (offF HOF.PL (HOF.PLO 2)) (offF HOF.POS (HOF.POSO 2))
    (offF HOF.SRT (HOF.SRTO 2)) (offF HOF.SRI (HOF.SRIO 2)) 900 450 = true := by quickRfl
theorem oE3_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 3)
    (offF HOF.T (HOF.TO 3)) (offF HOF.PL (HOF.PLO 3)) (offF HOF.POS (HOF.POSO 3))
    (offF HOF.SRT (HOF.SRTO 3)) (offF HOF.SRI (HOF.SRIO 3)) 0 450 = true := by quickRfl
theorem oE3_1 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 3)
    (offF HOF.T (HOF.TO 3)) (offF HOF.PL (HOF.PLO 3)) (offF HOF.POS (HOF.POSO 3))
    (offF HOF.SRT (HOF.SRTO 3)) (offF HOF.SRI (HOF.SRIO 3)) 450 450 = true := by quickRfl
theorem oE3_2 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 3)
    (offF HOF.T (HOF.TO 3)) (offF HOF.PL (HOF.PLO 3)) (offF HOF.POS (HOF.POSO 3))
    (offF HOF.SRT (HOF.SRTO 3)) (offF HOF.SRI (HOF.SRIO 3)) 900 450 = true := by quickRfl
theorem oE4_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 4)
    (offF HOF.T (HOF.TO 4)) (offF HOF.PL (HOF.PLO 4)) (offF HOF.POS (HOF.POSO 4))
    (offF HOF.SRT (HOF.SRTO 4)) (offF HOF.SRI (HOF.SRIO 4)) 0 450 = true := by quickRfl
theorem oE4_1 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 4)
    (offF HOF.T (HOF.TO 4)) (offF HOF.PL (HOF.PLO 4)) (offF HOF.POS (HOF.POSO 4))
    (offF HOF.SRT (HOF.SRTO 4)) (offF HOF.SRI (HOF.SRIO 4)) 450 450 = true := by quickRfl
theorem oE4_2 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 4)
    (offF HOF.T (HOF.TO 4)) (offF HOF.PL (HOF.PLO 4)) (offF HOF.POS (HOF.POSO 4))
    (offF HOF.SRT (HOF.SRTO 4)) (offF HOF.SRI (HOF.SRIO 4)) 900 450 = true := by quickRfl
theorem oE5_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 5)
    (offF HOF.T (HOF.TO 5)) (offF HOF.PL (HOF.PLO 5)) (offF HOF.POS (HOF.POSO 5))
    (offF HOF.SRT (HOF.SRTO 5)) (offF HOF.SRI (HOF.SRIO 5)) 0 450 = true := by quickRfl
theorem oE5_1 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 5)
    (offF HOF.T (HOF.TO 5)) (offF HOF.PL (HOF.PLO 5)) (offF HOF.POS (HOF.POSO 5))
    (offF HOF.SRT (HOF.SRTO 5)) (offF HOF.SRI (HOF.SRIO 5)) 450 450 = true := by quickRfl
theorem oE5_2 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 5)
    (offF HOF.T (HOF.TO 5)) (offF HOF.PL (HOF.PLO 5)) (offF HOF.POS (HOF.POSO 5))
    (offF HOF.SRT (HOF.SRTO 5)) (offF HOF.SRI (HOF.SRIO 5)) 900 450 = true := by quickRfl
theorem oE5_3 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 5)
    (offF HOF.T (HOF.TO 5)) (offF HOF.PL (HOF.PLO 5)) (offF HOF.POS (HOF.POSO 5))
    (offF HOF.SRT (HOF.SRTO 5)) (offF HOF.SRI (HOF.SRIO 5)) 1350 450 = true := by quickRfl
theorem oE5_4 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 5)
    (offF HOF.T (HOF.TO 5)) (offF HOF.PL (HOF.PLO 5)) (offF HOF.POS (HOF.POSO 5))
    (offF HOF.SRT (HOF.SRTO 5)) (offF HOF.SRI (HOF.SRIO 5)) 1800 450 = true := by quickRfl
theorem oE6_0 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 0 450 = true := by quickRfl
theorem oE6_1 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 450 450 = true := by quickRfl
theorem oE6_2 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 900 450 = true := by quickRfl
theorem oE6_3 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 1350 450 = true := by quickRfl
theorem oE6_4 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 1800 450 = true := by quickRfl
theorem oE6_5 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 2250 450 = true := by quickRfl
theorem oE6_6 : penumSlK 105 7 (mask 7) (105 * 7) true HOF.G HOF.GI HOF.k (HOF.C 6)
    (offF HOF.T (HOF.TO 6)) (offF HOF.PL (HOF.PLO 6)) (offF HOF.POS (HOF.POSO 6))
    (offF HOF.SRT (HOF.SRTO 6)) (offF HOF.SRI (HOF.SRIO 6)) 2700 450 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
