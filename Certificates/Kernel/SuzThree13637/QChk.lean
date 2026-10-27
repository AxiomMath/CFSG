module

public import Certificates.Kernel.SuzThree13637.QData
public import Certificates.Kernel.SuzThree13637.ClsData
public import Certificates.Kernel.SuzThree13637.Bind
public import Certificates.Data.Kernel.Spor.QMdlK
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.PSearch CFSG.KS.HypK CFSG.KS.QMdlK
  CertificateChecks.KernelSpor

theorem qrel_ok : relOK 1782 11 F.D Q0 Q1 Q2 QM.qr = true := by quickRfl

theorem qdist_ok : distOK (nthL F.M 0) (nthL F.M 1) = true := by quickRfl

theorem qfus_ok : fusOK (nthL F.M 0) (nthL F.M 1) (nthN QM.qr 1) (nthN QM.qr 2) QM.lc QM.fb = true := by
  quickRfl

theorem qtr_ok : trOK 1782 11 SuzC.LR SuzC.TRI SuzC.BP F.D Q1 Q2 CD.Y QM.lc QM.H QM.z = true := by
  quickRfl

end CFSG.KD.SuzThree13637

end
