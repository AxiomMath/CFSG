module

public import Certificates.Data.Kernel.E6PlaneLines

public section

namespace CertificateChecks.KernelE6PlaneLines

open CFSG.KC.E6PlaneLines CFSG.HardMathSupport.Timmesfeld.CrossChar

set_option maxHeartbeats 0 in
theorem lines_check_A : linesCheckWith (e6ThreeReps.take 4) nsMask 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem lines_check_B : linesCheckWith (e6ThreeReps.drop 4) nsMask 6 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ns_mask_check : nsMaskCheck () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pass_one_check : passOneCheck () = true := by
  decide +kernel

end CertificateChecks.KernelE6PlaneLines
