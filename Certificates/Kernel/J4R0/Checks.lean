module

public import Certificates.Kernel.J4R0.Data
public import Certificates.Data.Kernel.J4R0
public import Certificates.Kernel.J4Q.MatData
public import Certificates.Kernel.J4Q.QT2AData
public import Certificates.Kernel.J4Q.QTData
public import Certificates.Kernel.J4Q.MaskData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4R0

open CFSG.KC.J4R0 CFSG.KD.J4Q
open CFSG.KC.J4Q (getN notB)

@[expose] noncomputable def GLZ : List Nat :=
  [QA_0, QA_1, QA_2, QA_3, QA_4, QA_5, QA_6, QA_7, QA_8, QA_9, QA_10, QA_11, YA, YB, YP5, YP7,
    YP11, U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10, mkKM_0, mkKM_1, mkKM_2, mkKM_3]

theorem base_ok : baseOK c rm one GLZ BS XS TS B3I B4I = true := by quickRfl

theorem rel_ok : relOK c rm one XS CT SQ = true := by quickRfl

theorem sep_ok : sepOK rm one XS SEP = true := by quickRfl

theorem rad_ok : radOK CT RL = true := by quickRfl

theorem na_ok : normOK c rm one XS (getN one BS 4) NA = true := by quickRfl

theorem nb_ok : normOK c rm one XS (getN one BS 15) NB = true := by quickRfl

theorem ca_ok : coverOK c rm one XS TS (getN one BS 4) CA = true := by quickRfl

theorem cb_ok : coverOK c rm one XS TS (getN one BS 15) CB = true := by quickRfl

theorem gw_ok : gwOK c rm one XS BS (getN one BS 4) (getN one BS 15) GW = true := by quickRfl

theorem zb_ok : zbOK c rm one XS BS = true := by quickRfl

end CertificateChecks.KernelJ4R0
