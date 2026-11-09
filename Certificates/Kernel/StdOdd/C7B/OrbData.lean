module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C7B URT "Certificates/Kernel/StdOdd/data/c7B/orbplr.bin" 70861 4 11054316 8079208526212848927
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C7B NXT "Certificates/Kernel/StdOdd/data/c7B/orbnb.bin" 524288 4 22544384 9111896401973188026
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C7B cr "Certificates/Kernel/StdOdd/data/c7B/orbcr.txt" 14 15810222779583162482

@[expose] noncomputable def C7B.UR : List Nat := leafPl C7B.URT 566883 156

@[expose] noncomputable def C7B.NX : List Nat := leafPl C7B.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
