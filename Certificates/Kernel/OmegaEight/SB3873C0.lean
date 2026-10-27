
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E0

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand0 : t1KillC 0 16 0 false = true := by
  t1cenS cenQ0, cenB0

set_option maxHeartbeats 0 in
theorem cand1 : t1KillC 0 16 24 true = true := by
  t1cenS cenQ1, cenB1

set_option maxHeartbeats 0 in
theorem cand2 : t1KillC 0 17 0 true = true := by
  t1cenS cenQ2, cenB2

set_option maxHeartbeats 0 in
theorem cand3 : t1KillC 0 17 24 true = true := by
  t1cenS cenQ3, cenB3

set_option maxHeartbeats 0 in
theorem cand4 : t1KillC 0 18 0 true = true := by
  t1cenS cenQ4, cenB4

set_option maxHeartbeats 0 in
theorem cand5 : t1KillC 0 18 24 true = true := by
  t1cenS cenQ5, cenB5

set_option maxHeartbeats 0 in
theorem cand6 : t1KillC 0 19 0 true = true := by
  t1cenS cenQ6, cenB6

set_option maxHeartbeats 0 in
theorem cand7 : t1KillC 0 19 24 true = true := by
  t1cenS cenQ7, cenB7

set_option maxHeartbeats 0 in
theorem cand8 : t1KillC 0 20 0 true = true := by
  t1cenS cenQ8, cenB8

set_option maxHeartbeats 0 in
theorem cand9 : t1KillC 0 20 24 true = true := by
  t1cenS cenQ9, cenB9

end CertificateChecks.KernelO8.SB3873

end
