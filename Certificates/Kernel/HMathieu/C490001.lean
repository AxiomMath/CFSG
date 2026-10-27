module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.Pred24
public meta import CFSG.Certificates.Kernel.Common.JsonGz
public meta import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_json_gz CertificateChecks.KernelHMathieu.C490001
  "Certificates/Kernel/HMathieu/data/C1.json.gz" 372 17301024585504269729 (mS : Nat) (mT : Nat) (mF : List Nat)

namespace CertificateChecks.KernelHMathieu.C490001

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

set_option maxHeartbeats 0 in
theorem maskS : c1MaskS T24.P = mS := by decide +kernel

set_option maxHeartbeats 0 in
theorem maskT : c1MaskT T24.P = mT := by decide +kernel

set_option maxHeartbeats 0 in
theorem maskF : c1MaskF T24.P = mF := by decide +kernel

set_option maxHeartbeats 0 in
theorem search : gAllR 191 (fun st y => T24.Mc.getD y [] :: st)
    (fun L S _ => predC1K mS mT mF L S) 7 [] [191] (2 ^ 191 - 1) [] T24.rows 0 = true := by
  decide +kernel

end CertificateChecks.KernelHMathieu.C490001

end
