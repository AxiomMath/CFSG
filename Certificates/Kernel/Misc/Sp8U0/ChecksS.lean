module

public import Certificates.Data.Kernel.Misc.Sp8U0
public import Certificates.Data.Kernel.Misc.BfsKWStep
public import Certificates.Kernel.Misc.Sp8U0.Rec
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8U0

open CFSG.KD.BfsKW CFSG.KD.Sp8Syl3

#kc_each CFSG.KD.Sp8U0 ch899106S (fun j => stepSlW REC (rst REC) 9 65536 5 j) 0 32

theorem u06_neg_step :
    (!stepSlW REC (rst (fun i => cond (Nat.beq i 1) (REC 2) (REC i))) 9 65536 5 0) = true := by
  quickRfl

end CFSG.KD.Sp8U0

end
