module

public import Certificates.Kernel.EvenSporG24Hex.Data
import Certificates.Kernel.EvenSporG24Hex.Fast

public section

namespace CertificateChecks.KernelG24Hex

set_option maxHeartbeats 0 in
theorem hexF8 : hexF (nat_lit 8) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF9 : hexF (nat_lit 9) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF10 : hexF (nat_lit 10) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF11 : hexF (nat_lit 11) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF12 : hexF (nat_lit 12) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF13 : hexF (nat_lit 13) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF14 : hexF (nat_lit 14) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF15 : hexF (nat_lit 15) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

end CertificateChecks.KernelG24Hex

end
