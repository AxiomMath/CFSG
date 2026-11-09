module

public import Certificates.Kernel.Sporadic.OddCore.HL
public import Certificates.Data.Kernel.Spor.PEnumBC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeL

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt CFSG.KS.PEnumB

theorem oE7_0 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 0 450 = true := by quickRfl
theorem oE7_1 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 450 450 = true := by quickRfl
theorem oE7_2 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 900 450 = true := by quickRfl
theorem oE7_3 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 1350 450 = true := by quickRfl
theorem oE7_4 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 1800 450 = true := by quickRfl
theorem oE7_5 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 2250 450 = true := by quickRfl
theorem oE7_6 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 7)
    (offF HOF.T (HOF.TO 7)) (offF HOF.PL (HOF.PLO 7)) (offF HOF.POS (HOF.POSO 7))
    (offF HOF.SRT (HOF.SRTO 7)) (offF HOF.SRI (HOF.SRIO 7)) 2700 450 = true := by quickRfl
theorem oE8_0 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 0 450 = true := by quickRfl
theorem oE8_1 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 450 450 = true := by quickRfl
theorem oE8_2 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 900 450 = true := by quickRfl
theorem oE8_3 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 1350 450 = true := by quickRfl
theorem oE8_4 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 1800 450 = true := by quickRfl
theorem oE8_5 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 2250 450 = true := by quickRfl
theorem oE8_6 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 2700 450 = true := by quickRfl
theorem oE8_7 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 3150 450 = true := by quickRfl
theorem oE8_8 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 8)
    (offF HOF.T (HOF.TO 8)) (offF HOF.PL (HOF.PLO 8)) (offF HOF.POS (HOF.POSO 8))
    (offF HOF.SRT (HOF.SRTO 8)) (offF HOF.SRI (HOF.SRIO 8)) 3600 450 = true := by quickRfl
theorem oE9_0 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 0 450 = true := by quickRfl
theorem oE9_1 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 450 450 = true := by quickRfl
theorem oE9_2 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 900 450 = true := by quickRfl
theorem oE9_3 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 1350 450 = true := by quickRfl
theorem oE9_4 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 1800 450 = true := by quickRfl
theorem oE9_5 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 2250 450 = true := by quickRfl
theorem oE9_6 : penumSlBC 105 7 (mask 7) [0, 1, 2] HOF.G HOF.GI HOF.k (HOF.C 9)
    (offF HOF.T (HOF.TO 9)) (offF HOF.PL (HOF.PLO 9)) (offF HOF.POS (HOF.POSO 9))
    (offF HOF.SRT (HOF.SRTO 9)) (offF HOF.SRI (HOF.SRIO 9)) 2700 450 = true := by quickRfl

end CertificateChecks.KernelSpor.HeL

end
