module

public import Certificates.Kernel.GH74Tab.Data
public import Certificates.Kernel.GH74Tab.DataB
public import Certificates.Data.Kernel.GH74Tab.Pos

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab

theorem c5089_s2_6 : s2OK 6 B.S2 = true := by decide +kernel

theorem c5089_s2_7 : s2OK 7 B.S2 = true := by decide +kernel

theorem c5089_pos : posOK dat B.S2 dat.adm = true := by decide +kernel

end CFSG.KD.GH74Tab

end
