module

public import Certificates.Kernel.J1Dc.Defs
public import Certificates.Kernel.SporSch.Ru.RowsGen
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

#kss_each CFSG.KD.J1Dc.K CFSG.KD.J1Dc.ch 24

end
