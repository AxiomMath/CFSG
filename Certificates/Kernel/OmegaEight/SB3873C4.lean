
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E4

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand40 : t1KillC 1 20 0 true = true := by
  t1cenS cenQ40, cenB40

set_option maxHeartbeats 0 in
theorem cand41 : t1KillC 1 20 24 true = true := by
  t1cenS cenQ41, cenB41

set_option maxHeartbeats 0 in
theorem cand42 : t1KillC 1 21 0 true = true := by
  t1cenS cenQ42, cenB42

set_option maxHeartbeats 0 in
theorem cand43 : t1KillC 1 21 24 false = true := by
  t1cenS cenQ43, cenB43

set_option maxHeartbeats 0 in
theorem cand44 : t1KillC 1 22 0 true = true := by
  t1cenS cenQ44, cenB44

set_option maxHeartbeats 0 in
theorem cand45 : t1KillC 1 22 24 true = true := by
  t1cenS cenQ45, cenB45

set_option maxHeartbeats 0 in
theorem cand46 : t1KillC 1 23 0 true = true := by
  t1cenS cenQ46, cenB46

set_option maxHeartbeats 0 in
theorem cand47 : t1KillC 1 23 24 true = true := by
  t1cenS cenQ47, cenB47

set_option maxHeartbeats 0 in
theorem cand48 : t1KillC 1 24 0 true = true := by
  t1cenS cenQ48, cenB48

set_option maxHeartbeats 0 in
theorem cand49 : t1KillC 1 24 24 true = true := by
  t1cenS cenQ49, cenB49

end CertificateChecks.KernelO8.SB3873

end
