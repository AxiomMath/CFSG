module

import Certificates.Kernel.Ly3085.Omega.SwData
import CFSG.Certificates.Kernel.Common.EachTrue

namespace CFSG.KD.LyS3

#kc_each CFSG.KD.LyS3 s3 (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b) 2048 3072

end CFSG.KD.LyS3
