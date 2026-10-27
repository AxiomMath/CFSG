module

import Certificates.Kernel.Ly3085.O2.Data
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.LyO2

#kc_each CFSG.KD.LyO2 tree (fun b => CFSG.KC.LyOm.treeRange C KX PT P0 P1 n b 1) 14848 15137

#kc_repo #kc_each_rows CFSG.KD.LyO2 sort (fun _ k₀ c => CFSG.KC.LyOm.sortChunk KX SG n k₀ c)
  "Certificates/Kernel/Ly3085/O2/data/o2_sort.txt.gz" 3651 10905103381143264431 0 223

end CFSG.KD.LyO2
