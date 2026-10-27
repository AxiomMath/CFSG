
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand30 : t1KillC 0 31 0 false = true := by
  t1cenS cenQ30, cenB30

set_option maxHeartbeats 0 in
theorem cand31 : t1KillC 0 31 24 true = true := by
  t1cenS cenQ31, cenB31

set_option maxHeartbeats 0 in
theorem cand32 : t1KillC 1 16 0 true = true := by
  t1cenS cenQ32, cenB32

set_option maxHeartbeats 0 in
theorem cand33 : t1KillC 1 16 24 false = true := by
  t1cenS cenQ33, cenB33

set_option maxHeartbeats 0 in
theorem cand34 : t1KillC 1 17 0 true = true := by
  t1cenS cenQ34, cenB34

set_option maxHeartbeats 0 in
theorem cand35 : t1KillC 1 17 24 true = true := by
  t1cenS cenQ35, cenB35

set_option maxHeartbeats 0 in
theorem cand36 : t1KillC 1 18 0 true = true := by
  t1cenS cenQ36, cenB36

set_option maxHeartbeats 0 in
theorem cand37 : t1KillC 1 18 24 true = true := by
  t1cenS cenQ37, cenB37

set_option maxHeartbeats 0 in
theorem cand38 : t1KillC 1 19 0 true = true := by
  t1cenS cenQ38, cenB38

set_option maxHeartbeats 0 in
theorem cand39 : t1KillC 1 19 24 true = true := by
  t1cenS cenQ39, cenB39

end CertificateChecks.KernelO8.SB3873

end
