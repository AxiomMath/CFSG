module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C11 URT "Certificates/Kernel/StdOdd/data/c11/orbplr.bin" 45092 4 7034352 14899228909377260508
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C11 NXT "Certificates/Kernel/StdOdd/data/c11/orbnb.bin" 524288 4 22544384 12071461161064798211
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C11 cr "Certificates/Kernel/StdOdd/data/c11/orbcr.txt" 7 17433812592905998847

@[expose] noncomputable def C11.UR : List Nat := leafPl C11.URT 360735 156

@[expose] noncomputable def C11.NX : List Nat := leafPl C11.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
