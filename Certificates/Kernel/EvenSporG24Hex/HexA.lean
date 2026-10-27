module

public import Certificates.Kernel.EvenSporG24Hex.Data
import Certificates.Kernel.EvenSporG24Hex.Fast

public section

namespace CertificateChecks.KernelG24Hex

set_option maxHeartbeats 0 in
theorem hexF0 : hexF (nat_lit 0) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF1 : hexF (nat_lit 1) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF2 : hexF (nat_lit 2) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF3 : hexF (nat_lit 3) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF4 : hexF (nat_lit 4) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF5 : hexF (nat_lit 5) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF6 : hexF (nat_lit 6) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

set_option maxHeartbeats 0 in
theorem hexF7 : hexF (nat_lit 7) = true := by
  rw [hexF, hexJ_eq]
  decide +kernel

end CertificateChecks.KernelG24Hex

end
