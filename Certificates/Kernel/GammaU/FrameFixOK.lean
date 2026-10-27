module

public import Certificates.Data.Kernel.GammaUFrameFixK

public section

namespace CFSG.KD.GUX

open CFSG.KC.GUX

theorem ff16971_rowsG0 : rowsG 0 = true := by decide +kernel
theorem ff16971_rowsG1 : rowsG 1 = true := by decide +kernel
theorem ff16971_rowsC0 : rowsC 0 = true := by decide +kernel
theorem ff16971_rowsC1 : rowsC 1 = true := by decide +kernel
theorem ff16971_fix0 : fix 0 = true := by decide +kernel
theorem ff16971_fix1 : fix 1 = true := by decide +kernel
theorem ff16971_a0_0 : fixA 0 = true := by decide +kernel
theorem ff16971_a0_1 : fixA 1 = true := by decide +kernel
theorem ff16971_comm0 : comm 0 = true := by decide +kernel
theorem ff16971_comm1 : comm 1 = true := by decide +kernel
theorem ff16971_wit0 : wit 0 = true := by decide +kernel
theorem ff16971_wit1 : wit 1 = true := by decide +kernel
theorem ff16971_n2_0 : n2 0 = true := by decide +kernel
theorem ff16971_n2_1 : n2 1 = true := by decide +kernel

end CFSG.KD.GUX

end
