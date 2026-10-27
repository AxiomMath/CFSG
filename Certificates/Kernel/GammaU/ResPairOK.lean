module

public import Certificates.Kernel.GammaU.ResPair0Data
public import Certificates.Kernel.GammaU.ResPair1Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GURP0 cr16980a CFSG.KD.GURP0.rp 0 29
#kc_each CFSG.KD.GURP1 cr16980b CFSG.KD.GURP1.rp 0 29

namespace CFSG.KD.GURP0

open CFSG.KC.IF4C

#kc_forall_chunks cr16980a_all (fun j => rp j = true) 29 CFSG.KD.GURP0.cr16980a 1

theorem cr16980a_lists : lists = true := by decide +kernel

end CFSG.KD.GURP0

namespace CFSG.KD.GURP1

open CFSG.KC.IF4C

#kc_forall_chunks cr16980b_all (fun j => rp j = true) 29 CFSG.KD.GURP1.cr16980b 1

theorem cr16980b_lists : lists = true := by decide +kernel

end CFSG.KD.GURP1

end
