module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.MonsterB.Chain3042Data
meta import Certificates.Kernel.MonsterB.Chain3042Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.Chain3042.P2C 24 5 24 CertificateChecks.Chain3042.p2Strong
  CertificateChecks.Chain3042.p2Base 6 CertificateChecks.Chain3042.p2Der

end
