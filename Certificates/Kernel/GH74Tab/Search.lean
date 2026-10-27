module

public import Certificates.Kernel.GH74Tab.Data

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab

theorem c5042_data : dataOK dat = true := by decide +kernel

theorem c5042_search : searchOK dat = true := by decide +kernel

end CFSG.KD.GH74Tab

end
