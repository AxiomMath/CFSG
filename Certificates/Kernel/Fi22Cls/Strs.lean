module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi22Cls.RS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.labRepStr

#ks_chars CertificateChecks.KernelFi22Cls.CS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.labClsStr

#ks_chars CertificateChecks.KernelFi22Cls.WS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.conjStr

end
