module

import Certificates.Kernel.Ly3085.Omega.SwData
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.LyS3

#kc_each CFSG.KD.LyS3 s3 (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b) 6144 6358

#kc_repo #kc_each_rows CFSG.KD.LyS3 s3s (fun _ k₀ c => CFSG.KC.LyOm.sSort KX SG n k₀ c)
  "Certificates/Kernel/Ly3085/Omega/data/s3_sort.txt.gz" 1459 13556744538111603998 0 100

end CFSG.KD.LyS3
