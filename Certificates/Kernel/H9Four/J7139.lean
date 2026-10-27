module

public import Certificates.Data.Kernel.H9Four.J

set_option maxRecDepth 100000

public section

namespace CFSG.KD.H9Four.J

open CFSG.KC.H9Four.J

theorem ch7139_canon : canonDataK = true := by decide +kernel
theorem ch7139_s0 : s0CheckK = true := by decide +kernel
theorem ch7139_j0 : j0CheckK = true := by decide +kernel
theorem ch7139_x0 : x0CheckK = true := by decide +kernel
theorem ch7139_odd : oddGenCheckK = true := by decide +kernel
theorem ch7139_line : lineCheckK = true := by decide +kernel
theorem ch7139_fix : fixCheckK = true := by decide +kernel
theorem ch7139_ker : kerCheckK = true := by decide +kernel
theorem ch7139_e9 : e9CheckK = true := by decide +kernel
theorem ch7139_ff : ffRepCheckK = true := by decide +kernel
theorem ch7139_u0 : u0CheckK = true := by decide +kernel

end CFSG.KD.H9Four.J

end
