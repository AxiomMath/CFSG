module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C7A URT "Certificates/Kernel/StdOdd/data/c7A/orbplr.bin" 70859 4 11054004 8787188776595175180
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C7A NXT "Certificates/Kernel/StdOdd/data/c7A/orbnb.bin" 524288 4 22544384 6664646877884425311
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7A cr "Certificates/Kernel/StdOdd/data/c7A/orbcr.txt" 14 8628637653640945220

@[expose] noncomputable def C7A.UR : List Nat := leafPl C7A.URT 566865 156

@[expose] noncomputable def C7A.NX : List Nat := leafPl C7A.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
