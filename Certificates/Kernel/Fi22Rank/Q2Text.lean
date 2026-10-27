module

public import Certificates.Kernel.Fi22Rank.Q2Each
public import Certificates.Kernel.Sporadic.HexNumsGen
public import Certificates.Data.Kernel.Fi22Rk.Defs
public import Certificates.Data.Fi22TwistData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi22Rank.T CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.qGensHex2
#ks_hexnums CertificateChecks.KernelFi22Rank.T
  CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative.qGensHex2 3 12

namespace CertificateChecks.KernelFi22Rank.Q2

open CFSG.KC.Enum CFSG.KC.Fi22Rk

theorem rowsT : rowsK 3510 12 5 CertificateChecks.KernelFi22Rank.T.F (fun k => key (GI k)) = true := by
  quickRfl

end CertificateChecks.KernelFi22Rank.Q2

end
