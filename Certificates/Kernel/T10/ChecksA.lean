module

public import Certificates.Data.Kernel.T10CodeA

public section

namespace Certificates.Kernel.T10

open CFSG.KC.T10Code

theorem ch36401AO0 : orbOK PL orbD0 = true := by decide +kernel
theorem ch36401AO1 : orbOK PL orbD1 = true := by decide +kernel
theorem ch36401AO2 : orbOK PL orbD2 = true := by decide +kernel
theorem ch36401AO3 : orbOK PL orbD3 = true := by decide +kernel
theorem ch36401AO4 : orbOK PL orbD4 = true := by decide +kernel

theorem ch36401AL0 : allR (labOK PL) 0 128 = true := by decide +kernel
theorem ch36401AL1 : allR (labOK PL) 128 128 = true := by decide +kernel
theorem ch36401AL2 : allR (labOK PL) 256 128 = true := by decide +kernel
theorem ch36401AL3 : allR (labOK PL) 384 128 = true := by decide +kernel
theorem ch36401AL4 : allR (labOK PL) 512 128 = true := by decide +kernel
theorem ch36401AL5 : allR (labOK PL) 640 128 = true := by decide +kernel
theorem ch36401AL6 : allR (labOK PL) 768 128 = true := by decide +kernel
theorem ch36401AL7 : allR (labOK PL) 896 128 = true := by decide +kernel

theorem ch36401AK : allR (kchk PL) 0 25 = true := by decide +kernel

theorem ch36401AC : allR (clsOK PL) 0 25 = true := by decide +kernel

theorem ch36401AR : allR (rowOK PL) 0 25 = true := by decide +kernel

theorem ch36401AD : dfsM rowM leafM R25L 0 R25 = true := by decide +kernel

end Certificates.Kernel.T10
