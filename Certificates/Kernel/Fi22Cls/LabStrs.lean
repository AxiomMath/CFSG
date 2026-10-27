module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22ThreeInputs
import Certificates.Kernel.Sporadic.RawGen

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi22Cls.LOS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.labOfStr

#ks_chars CertificateChecks.KernelFi22Cls.WIS
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native.witOfStr

end
