module

public import Certificates.Data.Kernel.Misc.Sp8U0
public import Certificates.Data.Kernel.Misc.BfsKWWalk
public import Certificates.Kernel.Misc.Sp8U0.Rec
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CFSG.KD.Sp8U0

open CFSG.KD.BfsKW CFSG.KD.Sp8Syl3

#kc_each CFSG.KD.Sp8U0 ch899106B
  (fun j => buildSlW REC (rst REC) 9 65536 5 j && sortSlW REC 9 65536 j) 32 64

end CFSG.KD.Sp8U0

end
