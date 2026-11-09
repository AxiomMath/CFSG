module

public import Certificates.Kernel.HNFO4.Lits
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

#kc_each CFSG.KD.HNFO4 c (fun i => CFSG.KD.HNFO4.chkL i) 414 423
