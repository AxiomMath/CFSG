
module

public import Certificates.Kernel.LyFiveL1.Data
import CFSG.Certificates.Kernel.Common.Each

@[expose] public section

set_option maxRecDepth 400000

#kc_each CFSG.KD.LyFive.baseChk 0 100
