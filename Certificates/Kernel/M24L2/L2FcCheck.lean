module

public import Certificates.Data.Kernel.M24L2.FC
public import Certificates.Kernel.M24L2.DataB

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2

theorem dTwin_length : dTwin.all.length ≤ 2048 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem fc_ok : fcTreeK dL fcAllK2 thCodesK 3 [] = true := by decide +kernel

end CertificateChecks.KernelM24L2
