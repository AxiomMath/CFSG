
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E1

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand10 : t1KillC 0 21 0 false = true := by
  t1cenS cenQ10, cenB10

set_option maxHeartbeats 0 in
theorem cand11 : t1KillC 0 21 24 true = true := by
  t1cenS cenQ11, cenB11

set_option maxHeartbeats 0 in
theorem cand12 : t1KillC 0 22 0 true = true := by
  t1cenS cenQ12, cenB12

set_option maxHeartbeats 0 in
theorem cand13 : t1KillC 0 22 24 true = true := by
  t1cenS cenQ13, cenB13

set_option maxHeartbeats 0 in
theorem cand14 : t1KillC 0 23 0 true = true := by
  t1cenS cenQ14, cenB14

set_option maxHeartbeats 0 in
theorem cand15 : t1KillC 0 23 24 true = true := by
  t1cenS cenQ15, cenB15

set_option maxHeartbeats 0 in
theorem cand16 : t1KillC 0 24 0 true = true := by
  t1cenS cenQ16, cenB16

set_option maxHeartbeats 0 in
theorem cand17 : t1KillC 0 24 24 true = true := by
  t1cenS cenQ17, cenB17

set_option maxHeartbeats 0 in
theorem cand18 : t1KillC 0 25 0 true = true := by
  t1cenS cenQ18, cenB18

set_option maxHeartbeats 0 in
theorem cand19 : t1KillC 0 25 24 true = true := by
  t1cenS cenQ19, cenB19

end CertificateChecks.KernelO8.SB3873

end
