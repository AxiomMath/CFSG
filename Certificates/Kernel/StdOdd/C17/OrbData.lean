module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C17 URT "Certificates/Kernel/StdOdd/data/c17/orbplr.bin" 29177 4 4551612 14574813855938205275
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C17 NXT "Certificates/Kernel/StdOdd/data/c17/orbnb.bin" 524288 4 22544384 13900426954798517579
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C17 cr "Certificates/Kernel/StdOdd/data/c17/orbcr.txt" 4 15969335658916882722

@[expose] noncomputable def C17.UR : List Nat := leafPl C17.URT 233415 156

@[expose] noncomputable def C17.NX : List Nat := leafPl C17.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
