module

public import Certificates.Kernel.GH74Tab.Data
public import Certificates.Data.Kernel.GH74Tab.E1

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab

theorem c5042_e1_6 : e1OK dat 6 dat.adm = true := by decide +kernel

theorem c5042_e1_7 : e1OK dat 7 dat.adm7 = true := by decide +kernel

end CFSG.KD.GH74Tab

end
