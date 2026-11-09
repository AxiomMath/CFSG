module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C19 URT "Certificates/Kernel/StdOdd/data/c19/orbplr.bin" 26106 4 4072536 3973939710847098344
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C19 NXT "Certificates/Kernel/StdOdd/data/c19/orbnb.bin" 524288 4 22544384 367616908443163646
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C19 cr "Certificates/Kernel/StdOdd/data/c19/orbcr.txt" 3 13182415535504992591

@[expose] noncomputable def C19.UR : List Nat := leafPl C19.URT 208845 156

@[expose] noncomputable def C19.NX : List Nat := leafPl C19.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
