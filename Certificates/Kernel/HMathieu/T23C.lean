module

public import Certificates.Kernel.HMathieu.T23
public import Certificates.Data.Kernel.HMathieu.FixTab
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.T23C
  "Certificates/Kernel/HMathieu/data/T23C.json.gz" 22048 10950994843788063328
  (Mc : List (List Nat)) (F23c : List (List Nat)) (J23c : List (List Nat))

namespace CertificateChecks.KernelHMathieu.T23C

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem mcOK : Mc = T23.P.map (matP ccECols liftECols 11) := by decide +kernel

set_option maxHeartbeats 0 in
theorem tab : fixTabOK 11 (Mc.take 35) F23c J23c = true := by decide +kernel

end CertificateChecks.KernelHMathieu.T23C

end
