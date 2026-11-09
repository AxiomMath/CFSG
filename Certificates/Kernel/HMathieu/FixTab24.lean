module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.FixTab
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json CertificateChecks.KernelHMathieu.FixTab24
  "Certificates/Kernel/HMathieu/data/FixTab24.json" 81743 9741700353172737328
  (F24 : List (List Nat)) (J24 : List (List Nat))

namespace CertificateChecks.KernelHMathieu.FixTab24

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem tab : fixTabOK 11 (T24.Mc.take 191) F24 J24 = true := by decide +kernel

end CertificateChecks.KernelHMathieu.FixTab24

end
