
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E5

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand50 : t1KillC 1 25 0 true = true := by
  t1cenS cenQ50, cenB50

set_option maxHeartbeats 0 in
theorem cand51 : t1KillC 1 25 24 true = true := by
  t1cenS cenQ51, cenB51

set_option maxHeartbeats 0 in
theorem cand52 : t1KillC 1 26 0 true = true := by
  t1cenS cenQ52, cenB52

set_option maxHeartbeats 0 in
theorem cand53 : t1KillC 1 26 24 false = true := by
  t1cenS cenQ53, cenB53

set_option maxHeartbeats 0 in
theorem cand54 : t1KillC 1 27 0 true = true := by
  t1cenS cenQ54, cenB54

set_option maxHeartbeats 0 in
theorem cand55 : t1KillC 1 27 24 true = true := by
  t1cenS cenQ55, cenB55

set_option maxHeartbeats 0 in
theorem cand56 : t1KillC 1 28 0 true = true := by
  t1cenS cenQ56, cenB56

set_option maxHeartbeats 0 in
theorem cand57 : t1KillC 1 28 24 true = true := by
  t1cenS cenQ57, cenB57

set_option maxHeartbeats 0 in
theorem cand58 : t1KillC 1 29 0 true = true := by
  t1cenS cenQ58, cenB58

set_option maxHeartbeats 0 in
theorem cand59 : t1KillC 1 29 24 true = true := by
  t1cenS cenQ59, cenB59

end CertificateChecks.KernelO8.SB3873

end
