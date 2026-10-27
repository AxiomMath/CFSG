module

public import Certificates.Kernel.SporSch.MatSchGen
public import Certificates.Kernel.MonsterB.Chain3025Data
meta import Certificates.Kernel.MonsterB.Chain3025Data

public section

set_option maxRecDepth 400000

#ks_matsch CertificateChecks.Chain3025.Co2M 2300 12 22 16 64 0
  CertificateChecks.Chain3025.strongM CertificateChecks.Chain3025.baseM 2
  CertificateChecks.Chain3025.co2Der CertificateChecks.Chain3025.vecsM

end
