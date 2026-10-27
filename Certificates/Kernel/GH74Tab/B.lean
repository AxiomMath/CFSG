module

public import Certificates.Kernel.GH74Tab.Data
public import Certificates.Kernel.GH74Tab.DataB
public import Certificates.Data.Kernel.GH74Tab.B

public section

namespace CFSG.KD.GH74Tab

open CFSG.KC.GH74Tab

theorem c5038_trans6 : transB 6 B.Astar B.N4 B.N8 = true := by decide +kernel

theorem c5038_trans7 : transB 7 B.Astar B.N4 B.N8 = true := by decide +kernel

theorem c5038_b : bOK dat B.Astar B.N4 B.N8 B.Psi dat.adm B.W6 = true := by decide +kernel

end CFSG.KD.GH74Tab

end
