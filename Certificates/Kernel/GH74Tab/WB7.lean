module

public import Certificates.Kernel.GH74Tab.Data
public import Certificates.Data.Kernel.GH74Tab.WB

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab

theorem c5042_wb7 : wbOK dat 7 = true := by decide +kernel

end CFSG.KD.GH74Tab

end
