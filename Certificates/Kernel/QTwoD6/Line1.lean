module

import Certificates.Data.Kernel.QTwoD6K
import Certificates.Kernel.QTwoD6.Forms1
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 l1w
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowK 16129 CFSG.KD.QTwoD6.forms1 CFSG.KD.QTwoD6.surv1
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/wit1.txt.gz" 14014 11266799030176906053 0 999
