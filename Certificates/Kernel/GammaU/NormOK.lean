module

public import Certificates.Kernel.GammaU.Norm0Data
public import Certificates.Kernel.GammaU.Norm1Data
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000

public section

#kc_each CFSG.KD.GUN0 cn16966anl CFSG.KD.GUN0.nl 0 6
#kc_each CFSG.KD.GUN0 cn16966acv CFSG.KD.GUN0.cv 0 15
#kc_each CFSG.KD.GUN0 cn16966arp CFSG.KD.GUN0.rp 0 6
#kc_each CFSG.KD.GUN1 cn16966bnl CFSG.KD.GUN1.nl 0 6
#kc_each CFSG.KD.GUN1 cn16966bcv CFSG.KD.GUN1.cv 0 15
#kc_each CFSG.KD.GUN1 cn16966brp CFSG.KD.GUN1.rp 0 6

namespace CFSG.KD.GUN0

theorem cn16966a_lists : lists = true := by decide +kernel

end CFSG.KD.GUN0

namespace CFSG.KD.GUN1

theorem cn16966b_lists : lists = true := by decide +kernel

end CFSG.KD.GUN1

end
