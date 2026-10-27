module

public import Certificates.Kernel.Sporadic.RawGenSplitP
public import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Assembly.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG24.Tri27206

meta def baseM : Array Nat := CFSG.Sporadic.Co1Block.twoBChainBase.toArray

end CertificateChecks.KernelG24.Tri27206

end

#ks_rawchain_sl2_data CertificateChecks.KernelG24.Tri27206.LC 1365 11 0 128
  CFSG.Sporadic.Co1Block.twoBStrong CertificateChecks.KernelG24.Tri27206.baseM 2
  CFSG.Sporadic.Co1Block.twoBChainWords
#ks_rawchain_sl2_lvpCertificateChecks.KernelG24.Tri27206.LC 0 0 11
#ks_rawchain_sl2_lvpCertificateChecks.KernelG24.Tri27206.LC 1 0 11
#ks_rawchain_sl2_lvpCertificateChecks.KernelG24.Tri27206.LC 2 0 11
#ks_rawchain_sl2_join CertificateChecks.KernelG24.Tri27206.LC
