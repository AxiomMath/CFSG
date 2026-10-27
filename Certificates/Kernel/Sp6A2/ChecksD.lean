module

public import Certificates.Data.Kernel.Sp6A2K
public import Certificates.Kernel.Sp6A2.Rec
public import Certificates.Kernel.Sp62.Rec
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CFSG.KD.Sp6A2

#kc_each ch799751d i (fun i => dRows CFSG.KD.Sp62.REC REC 17715 5661 5668 (Nat.mul 6 i) 6) 0 6

end CFSG.KD.Sp6A2

end
