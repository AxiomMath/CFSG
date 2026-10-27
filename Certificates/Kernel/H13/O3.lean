module

public import CFSG.Quasithin.H13.L32NO3Inputs
import Certificates.Kernel.H13.O3Sub
import Certificates.Kernel.H13.O3Ov
import Certificates.Kernel.H13.O3Cen
public import Mathlib

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.Mat8Cert CFSG.Quasithin.H13.O3Cert

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
theorem o3_basicB_true : CFSG.Quasithin.H13.O3Cert.basicB = true := by
  simp only [CFSG.Quasithin.H13.O3Cert.basicB, o3_sub_om3, o3_sub_om3F, o3_sub_omN, o3_sub_h1,
    o3_sub_h2, Bool.true_and]
  o3_tac

theorem o3Check_true : o3Check = true := by
  simp only [o3Check, List.all_cons, List.all_nil, o3_basicB_true, o3_h1B_true, o3_pB0, o3_pB1,
    o3_wB0, o3_wB1, o3_invB0, o3_invB1, o3_ovB0, o3_ovB1, o3_kB0, o3_kB1, o3_cenB0, o3_cenB1,
    Bool.and_true]

end CertificateChecks.KernelH13

end
