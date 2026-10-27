module

public import Certificates.Kernel.E6WK.Data
import all Certificates.Data.Kernel.E6WK
import all Certificates.Data.TwE6WeylKill
import all CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

namespace CertificateChecks.KernelE6WK

open CFSG.KC.E6WK CFSG.KD.E6WK CFSG.HardMathSupport.Timmesfeld.Steinberg

set_option maxHeartbeats 0 in
theorem tab_check : tabCheckWith vp ir rm = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem up_check : upCheckWith ir words up = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem k_check : kCheckWith up = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem v_check : vCheckWith ir vk (KTree.ofSorted vk) = true := by
  decide +kernel

theorem up_wit_length : up.length = 27 ∧ wit.length = 27 := by
  decide +kernel

end CertificateChecks.KernelE6WK
