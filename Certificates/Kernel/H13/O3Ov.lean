module

public import Certificates.Kernel.H13.O3Tac

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.O3Cert

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem o3_ovB0 : CFSG.Quasithin.H13.O3Cert.ovB 0 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_ovB1 : CFSG.Quasithin.H13.O3Cert.ovB 1 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_kB0 : kB 0 = true := by o3_tac

set_option maxHeartbeats 0 in
theorem o3_kB1 : kB 1 = true := by o3_tac

end CertificateChecks.KernelH13

end
