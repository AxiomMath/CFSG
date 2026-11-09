module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C13 URT "Certificates/Kernel/StdOdd/data/c13/orbplr.bin" 38155 4 5952180 4394574811827187931
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C13 NXT "Certificates/Kernel/StdOdd/data/c13/orbnb.bin" 524288 4 22544384 11093789138184598194
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C13 cr "Certificates/Kernel/StdOdd/data/c13/orbcr.txt" 7 8486859514399454982

@[expose] noncomputable def C13.UR : List Nat := leafPl C13.URT 305235 156

@[expose] noncomputable def C13.NX : List Nat := leafPl C13.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
