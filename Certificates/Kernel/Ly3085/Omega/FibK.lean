module

import Certificates.Kernel.Ly3085.Omega.FibData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.LyF3

#kc_each CFSG.KD.LyF3 f3 (fun b => CFSG.KC.LyOm.cRange BC KX PT WT GT WC nc n b 1) 0 1

#kc_repo #kc_each_rows CFSG.KD.LyF3 f3s (fun _ k₀ c => CFSG.KC.LyOm.cSort KX PT SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/f3_sort.txt.gz" 6 11303616441619586069 0 1

end CFSG.KD.LyF3

namespace CFSG.KD.LyF4

#kc_each CFSG.KD.LyF4 f4 (fun b => CFSG.KC.LyOm.cRange BC KX PT WT GT WC nc n b 1) 0 12

#kc_repo #kc_each_rows CFSG.KD.LyF4 f4s (fun _ k₀ c => CFSG.KC.LyOm.cSort KX PT SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/f4_sort.txt.gz" 8 13255224151415772645 0 1

end CFSG.KD.LyF4
