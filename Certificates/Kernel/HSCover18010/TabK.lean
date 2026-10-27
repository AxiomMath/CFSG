module

public import Certificates.Data.Kernel.TabMat
public import Certificates.Kernel.VecCert.HS
public import Certificates.Kernel.HSCover18010.TabData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelHS18010

open CFSG.KC.TabMat CertificateChecks.KernelVec.HS CFSG.Sporadic.HS.Native

theorem tabK : tabMatK (hsData ()).d NA NAi NB NBi CFSG.KHS18010.G CFSG.KHS18010.Q = true := by
  quickRfl

end CertificateChecks.KernelHS18010

end
