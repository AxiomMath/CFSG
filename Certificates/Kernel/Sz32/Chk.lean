module

public import Certificates.Data.Kernel.Sz32Twin

public section

namespace CFSG.KC.Sz32T

theorem rows_0 : rowsOk wits 0 = true := by decide +kernel
theorem rows_1 : rowsOk wits 1 = true := by decide +kernel
theorem rows_2 : rowsOk wits 2 = true := by decide +kernel
theorem rows_3 : rowsOk wits 3 = true := by decide +kernel
theorem rows_4 : rowsOk wits 4 = true := by decide +kernel
theorem rows_5 : rowsOk wits 5 = true := by decide +kernel
theorem rows_6 : rowsOk wits 6 = true := by decide +kernel
theorem rows_7 : rowsOk wits 7 = true := by decide +kernel

theorem infty_ok : inftyOk wits = true := by decide +kernel

theorem chain_ok : chainOk = true := by decide +kernel

end CFSG.KC.Sz32T

end
