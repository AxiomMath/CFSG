
module

public import Certificates.Kernel.OmegaEight.SB3873GS
public import Certificates.Kernel.OmegaEight.SB3873E6

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen

set_option maxHeartbeats 0 in
theorem cand60 : t1KillC 1 30 0 true = true := by
  t1cenS cenQ60, cenB60

set_option maxHeartbeats 0 in
theorem cand61 : t1KillC 1 30 24 true = true := by
  t1cenS cenQ61, cenB61

set_option maxHeartbeats 0 in
theorem cand62 : t1KillC 1 31 0 true = true := by
  t1cenS cenQ62, cenB62

set_option maxHeartbeats 0 in
theorem cand63 : t1KillC 1 31 24 false = true := by
  t1cenS cenQ63, cenB63

end CertificateChecks.KernelO8.SB3873

end
