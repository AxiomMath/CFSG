module

public import Certificates.Kernel.HMathieu.T23
public import Certificates.Data.Kernel.HMathieu.FixTab
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.T23X
  "Certificates/Kernel/HMathieu/data/T23X.json.gz" 23747 2122766799374387369
  (rows : List (Nat × Nat)) (F23 : List (List Nat)) (J23 : List (List Nat))

namespace CertificateChecks.KernelHMathieu.T23X

open CFSG.KC.HMathieu CertificateChecks.KernelHMathieu

theorem rowsLen : rows.length = 35 := by decide +kernel

set_option maxHeartbeats 0 in
theorem tabs : tabsK 35 T23.P rows = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem tab : fixTabOK 11 (T23.Md.take 35) F23 J23 = true := by decide +kernel

end CertificateChecks.KernelHMathieu.T23X

end
