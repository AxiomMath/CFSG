module

public import Certificates.Kernel.HMathieu.T22
public import Certificates.Data.Kernel.HMathieu.FixTab
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.FixTab22
  "Certificates/Kernel/HMathieu/data/FixTab22.json.gz" 20755 9763986603196458015
  (F22 : List (List Nat)) (J22 : List (List Nat))

namespace CertificateChecks.KernelHMathieu.FixTab22

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem tab : fixTabOK 10 (T22.Mc.take 71) F22 J22 = true := by decide +kernel

end CertificateChecks.KernelHMathieu.FixTab22

end
