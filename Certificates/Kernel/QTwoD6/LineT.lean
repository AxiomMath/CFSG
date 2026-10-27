module

import Certificates.Data.Kernel.QTwoD6K2
import Certificates.Kernel.QTwoD6.FormsT
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 lTw
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowT CFSG.KD.QTwoD6.formsT CFSG.KD.QTwoD6.survT
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/witT.txt.gz" 23537 1495449710492393299 0 1639
