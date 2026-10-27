module

import Certificates.Data.Kernel.QTwoD6K2
import Certificates.Kernel.QTwoD6.Forms0
import Certificates.Kernel.QTwoD6.Forms1
import Certificates.Kernel.QTwoD6.Forms2
import Certificates.Kernel.QTwoD6.FormsT
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 t0w
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowK true CFSG.KD.QTwoD6.forms0 CFSG.KD.QTwoD6.surv0
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/tw0.txt.gz" 256 3999738995113224570 0 16

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 t1w
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowK false CFSG.KD.QTwoD6.forms1 CFSG.KD.QTwoD6.surv1
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/tw1.txt.gz" 196 1396833856800984709 0 12

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 t2w
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowK false CFSG.KD.QTwoD6.forms2 CFSG.KD.QTwoD6.surv2
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/tw2.txt.gz" 232 6909237699568378479 0 12

#kc_repo #kc_each_rows CFSG.KD.QTwoD6 tTw
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowT CFSG.KD.QTwoD6.formsT CFSG.KD.QTwoD6.survT
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/twT.txt.gz" 158 5178982405604147952 0 12
