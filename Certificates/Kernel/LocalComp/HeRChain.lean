module

public import Certificates.Kernel.Sporadic.RawGenSch3G
public import Certificates.Data.HeRCentData
public import Certificates.Kernel.LocalComp.HeRStrongData
meta import Certificates.Kernel.LocalComp.HeRStrongData
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.HeR

@[expose] def heRDerivs : List (List Int) :=
  CFSG.ComponentClassification.AS81.HePres.Native.heRChainWords.toList.drop 2

end CertificateChecks.KernelLC.HeR

#kc_repo #kc_json_gz CertificateChecks.KernelLC.HeRW
  "Certificates/Kernel/LocalComp/data/herw.json.gz" 241 7302964811756470322
  (W : List (List Nat))

set_option Elab.async false

#ks_rawchain_sl3g CertificateChecks.KernelLC.HeRC 8330 14 1 8 0
  CertificateChecks.KernelLC.HeR.heRStrongLit CertificateChecks.KernelLC.HeR.heRBaseLit 2
  CertificateChecks.KernelLC.HeR.heRDerivs (0 1) CertificateChecks.KernelLC.HeRW.W

end
