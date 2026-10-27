module

import Certificates.Kernel.Ly3085.Omega.O1Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.LyO1

#kc_each CFSG.KD.LyO1 o1 (fun b => CFSG.KC.LyOm.cRange BC KX PT WT GT WC nc n b 1) 0 306

#kc_repo #kc_each_rows CFSG.KD.LyO1 o1s (fun _ k₀ c => CFSG.KC.LyOm.cSort KX PT SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/o1_sort.txt.gz" 255 10065935069105506461 0 20

#kc_repo #kc_each_rows CFSG.KD.LyO1 o1fTA (fun b c => Nat.beq (CFSG.KC.LyOm.cFix BC KX PT TA n b 1) c)
  "Certificates/Kernel/Ly3085/Omega/data/o1_fix_TA.txt.gz" 1726 3300370825710304508 0 186

end CFSG.KD.LyO1
