module

public import Certificates.Kernel.SporSch.PairJ3.ClData
public import Certificates.Kernel.SporSch.PairJ3.GenCnt
public meta import CFSG.Sporadic.Schreier.PairJ3CheckInputs

namespace CertificateChecks.KernelSporSch.PJ3NIn

meta def js : String := include_str "CntData.json"

end CertificateChecks.KernelSporSch.PJ3NIn

#kss_cntdata CertificateChecks.KernelSporSch.PJ3N 6156 13 CFSG.Sporadic.Schreier.PairJ3.levels
  CFSG.Sporadic.Schreier.PairJ3.bs CFSG.Sporadic.Schreier.PairJ3.cl
  CertificateChecks.KernelSporSch.PJ3NIn.js 171 512
