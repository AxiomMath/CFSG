module

public import Certificates.Data.Kernel.E6O2
public import Certificates.Kernel.E6O2.Data
public import Certificates.Kernel.E6Syl3.Data

public section

namespace CFSG.KD.E6O2

open CFSG.KC.E6O2

theorem ch214104_t2 : pcTups 2 g2 = t2 := by decide +kernel

theorem ch214104_t5 : pcTups 5 g5 = t5 := by decide +kernel

theorem ch214104_s2 : subCheck g2 128 t2 = true := by decide +kernel

theorem ch214104_s5 : subCheck g5 5 t5 = true := by decide +kernel

theorem ch214104_w2 : o2Check t2 w2 = true := by decide +kernel

theorem ch214104_w3 : o2Check CFSG.KD.E6Syl3.qt w3 = true := by decide +kernel

theorem ch214104_w5 : o2Check t5 w5 = true := by decide +kernel

end CFSG.KD.E6O2
