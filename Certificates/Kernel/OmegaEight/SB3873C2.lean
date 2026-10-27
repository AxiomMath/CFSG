
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand20 : t1KillC 0 26 0 false = true := by
  t1cenS cenQ20, cenB20

set_option maxHeartbeats 0 in
theorem cand21 : t1KillC 0 26 24 true = true := by
  t1cenS cenQ21, cenB21

set_option maxHeartbeats 0 in
theorem cand22 : t1KillC 0 27 0 true = true := by
  t1cenS cenQ22, cenB22

set_option maxHeartbeats 0 in
theorem cand23 : t1KillC 0 27 24 true = true := by
  t1cenS cenQ23, cenB23

set_option maxHeartbeats 0 in
theorem cand24 : t1KillC 0 28 0 true = true := by
  t1cenS cenQ24, cenB24

set_option maxHeartbeats 0 in
theorem cand25 : t1KillC 0 28 24 true = true := by
  t1cenS cenQ25, cenB25

set_option maxHeartbeats 0 in
theorem cand26 : t1KillC 0 29 0 true = true := by
  t1cenS cenQ26, cenB26

set_option maxHeartbeats 0 in
theorem cand27 : t1KillC 0 29 24 true = true := by
  t1cenS cenQ27, cenB27

set_option maxHeartbeats 0 in
theorem cand28 : t1KillC 0 30 0 true = true := by
  t1cenS cenQ28, cenB28

set_option maxHeartbeats 0 in
theorem cand29 : t1KillC 0 30 24 true = true := by
  t1cenS cenQ29, cenB29

end CertificateChecks.KernelO8.SB3873

end
