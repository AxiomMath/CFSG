module

public import Certificates.Kernel.Pk442010.Grp

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KC.A45Cls CFSG.KC.Pk442010

theorem ns : nsK CP.N CP.T rQ1 tAL = true ∧ nsK CP.N CP.T rQ2 tAL = true := by decide +kernel

theorem noOdd : noOddK CP.N CP.T nAW = true ∧ ord9K CP.N CP.T = true ∧
    noOddK CQ.N CQ.T nBW = true ∧ ord9K CQ.N CQ.T = true := by
  decide +kernel

theorem u : uK CQ.N CQ.T uW = true := by decide +kernel

theorem pair : pairK CP.N CP.T rQ1 rQ2 tAL = true := by decide +kernel

end CertificateChecks.KernelPk442010

end
