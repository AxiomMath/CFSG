module

public import Certificates.Kernel.HMathieu.T12
public import Certificates.Data.Kernel.HMathieu.FixTab
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.FixTab12
  "Certificates/Kernel/HMathieu/data/FixTab12.json.gz" 8207 6090279697636045439
  (F12 : List (List Nat)) (J12 : List (List Nat))

namespace CertificateChecks.KernelHMathieu.FixTab12

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem tab : fixTabOK 10 (T12.Mc.take 35) F12 J12 = true := by decide +kernel

end CertificateChecks.KernelHMathieu.FixTab12

end
