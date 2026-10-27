module

public import Certificates.Data.Kernel.QTwoD6K2
public import Certificates.Kernel.QTwoD6.Forms0
public import Certificates.Kernel.QTwoD6.Forms1
public import Certificates.Kernel.QTwoD6.Forms2
public import Certificates.Kernel.QTwoD6.FormsT
import Certificates.Kernel.QTwoD6.Line0
import Certificates.Kernel.QTwoD6.Line1
import Certificates.Kernel.QTwoD6.Line2
import Certificates.Kernel.QTwoD6.LineT
import Certificates.Kernel.QTwoD6.Twist
import CFSG.Certificates.Kernel.Common.RowsForall
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.l0_all
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowK 16128 CFSG.KD.QTwoD6.forms0 CFSG.KD.QTwoD6.surv0
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/wit0.txt.gz" 14081 12987558263078488158 0 1005
  CFSG.KD.QTwoD6.l0w

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.l1_all
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowK 16129 CFSG.KD.QTwoD6.forms1 CFSG.KD.QTwoD6.surv1
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/wit1.txt.gz" 14014 11266799030176906053 0 999
  CFSG.KD.QTwoD6.l1w

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.l2_all
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowK 127 CFSG.KD.QTwoD6.forms2 CFSG.KD.QTwoD6.surv2
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/wit2.txt.gz" 14003 8473265770080787838 0 999
  CFSG.KD.QTwoD6.l2w

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.lT_all
  (fun i kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.rowT CFSG.KD.QTwoD6.formsT CFSG.KD.QTwoD6.survT
    i kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/witT.txt.gz" 23537 1495449710492393299 0 1639
  CFSG.KD.QTwoD6.lTw

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.t0_all
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowK true CFSG.KD.QTwoD6.forms0 CFSG.KD.QTwoD6.surv0
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/tw0.txt.gz" 256 3999738995113224570 0 16
  CFSG.KD.QTwoD6.t0w

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.t1_all
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowK false CFSG.KD.QTwoD6.forms1 CFSG.KD.QTwoD6.surv1
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/tw1.txt.gz" 196 1396833856800984709 0 12
  CFSG.KD.QTwoD6.t1w

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.t2_all
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowK false CFSG.KD.QTwoD6.forms2 CFSG.KD.QTwoD6.surv2
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/tw2.txt.gz" 232 6909237699568378479 0 12
  CFSG.KD.QTwoD6.t2w

#kc_repo #kc_rows_forall CFSG.KD.QTwoD6.tT_all
  (fun j kd g₁ w₁ g₂ w₂ => CFSG.KC.QTwoD6K.twRowT CFSG.KD.QTwoD6.formsT CFSG.KD.QTwoD6.survT
    j kd g₁ w₁ g₂ w₂)
  "Certificates/Kernel/QTwoD6/data/twT.txt.gz" 158 5178982405604147952 0 12
  CFSG.KD.QTwoD6.tTw

end
