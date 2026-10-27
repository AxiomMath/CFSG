module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co2Cert.Data
public meta import CFSG.Sporadic.Co2Cert.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co2

@[expose] def derivA : List (List Int) := CFSG.Sporadic.Co2Cert.co2Rec.chain.derivations

end CertificateChecks.KernelSpor.Co2

#ks_rawchain_sl2_data CertificateChecks.KernelSpor.Co2A 2300 12 0 16
  CFSG.Sporadic.Co2Cert.co2StrongArrs CFSG.Sporadic.Co2Cert.co2BaseArr 2
  CertificateChecks.KernelSpor.Co2.derivA

end
