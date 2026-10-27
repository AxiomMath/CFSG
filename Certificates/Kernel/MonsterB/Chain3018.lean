module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.MonsterB.Chain3018Data
meta import Certificates.Kernel.MonsterB.Chain3018Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.Chain3018.C1C 24 5 24 CertificateChecks.Chain3018.c1Strong
  CertificateChecks.Chain3018.c1Base 5 CertificateChecks.Chain3018.c1Der

#ks_rawchain CertificateChecks.Chain3018.C2C 24 5 24 CertificateChecks.Chain3018.c2Strong
  CertificateChecks.Chain3018.c2Base 5 CertificateChecks.Chain3018.c2Der

end
