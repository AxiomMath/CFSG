module

public import Certificates.Data.Kernel.T10Code

public section

namespace Certificates.Kernel.T10

open CFSG.KC.T10Code

theorem ch36401T : (cTc PL == 128 && iTc PL == 55) = true := by decide +kernel

theorem ch36401B0 : allR (FB PL) 0 128 = true := by decide +kernel
theorem ch36401B1 : allR (FB PL) 128 128 = true := by decide +kernel
theorem ch36401B2 : allR (FB PL) 256 128 = true := by decide +kernel
theorem ch36401B3 : allR (FB PL) 384 128 = true := by decide +kernel
theorem ch36401B4 : allR (FB PL) 512 128 = true := by decide +kernel
theorem ch36401B5 : allR (FB PL) 640 128 = true := by decide +kernel
theorem ch36401B6 : allR (FB PL) 768 128 = true := by decide +kernel
theorem ch36401B7 : allR (FB PL) 896 128 = true := by decide +kernel

theorem ch36401C0 : allR (FC PL) 0 128 = true := by decide +kernel
theorem ch36401C1 : allR (FC PL) 128 128 = true := by decide +kernel
theorem ch36401C2 : allR (FC PL) 256 128 = true := by decide +kernel
theorem ch36401C3 : allR (FC PL) 384 128 = true := by decide +kernel
theorem ch36401C4 : allR (FC PL) 512 128 = true := by decide +kernel
theorem ch36401C5 : allR (FC PL) 640 128 = true := by decide +kernel
theorem ch36401C6 : allR (FC PL) 768 128 = true := by decide +kernel
theorem ch36401C7 : allR (FC PL) 896 128 = true := by decide +kernel

end Certificates.Kernel.T10
