module

public import Certificates.Kernel.SporSch.PairHS.GenCnt

namespace CertificateChecks.KernelSporSch.PHSNIn

meta def js : String := include_str "CntData.json"

end CertificateChecks.KernelSporSch.PHSNIn

#kss_cnthsdata CertificateChecks.KernelSporSch.PHSN 12 CertificateChecks.KernelSporSch.PHSNIn.js
