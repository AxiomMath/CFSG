module

import Certificates.Data.Kernel.QTwoD6K
import Certificates.Kernel.QTwoD6.Forms2
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 l2w
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowK 127 CFSG.KD.QTwoD6.forms2 CFSG.KD.QTwoD6.surv2
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/wit2.txt.gz" 14003 8473265770080787838 0 999
