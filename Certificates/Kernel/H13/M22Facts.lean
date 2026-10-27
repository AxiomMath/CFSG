module

public import Certificates.Kernel.H13.M22A
public import Certificates.Kernel.H13.M22B
public import Certificates.Kernel.H13.M22Ov
public import Certificates.Kernel.H13.M22Ov4

public section

namespace CertificateChecks.KernelH13

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H13.M22Cert

theorem m22_ovB_true : ovB = true := by
  rw [m22_ovB_split, m22_ov1_true, m22_ov2_true, m22_ov3_true, m22_ov4_true, m22_ov5_true]
  rfl

theorem m22Check_true : m22Check = true := by
  rw [m22Check, m22_orbB_true, m22_s0B_true, m22_schB_true, m22_pB_true, m22_e0B_true,
    m22_witB_true, m22_ovB_true, m22_oB_true, m22_m12B_true]
  decide +kernel

end CertificateChecks.KernelH13

end
