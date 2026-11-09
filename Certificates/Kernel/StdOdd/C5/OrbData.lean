module

public import Certificates.Kernel.StdOdd.CentLeafPl
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain

#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C5 URT "Certificates/Kernel/StdOdd/data/c5/plr.bin" 99212 4 15477072 13202743628292324109
#kc_repo #kc_ktree CFSG.KD.StdOdd.Cent.C5 NXT "Certificates/Kernel/StdOdd/data/c5/nb.bin" 524288 4 22544384 7680349717441372748
#kc_repo #kc_natList CFSG.KD.StdOdd.Cent.C5 cr "Certificates/Kernel/StdOdd/data/c5/cr.txt" 19 1415251581434628912

@[expose] noncomputable def C5.UR : List Nat := leafPl C5.URT 793695 156

@[expose] noncomputable def C5.NX : List Nat := leafPl C5.NXT 4194304 43

end CFSG.KD.StdOdd.Cent

end
