module

public import Certificates.Kernel.J4.Data

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4.R CFSG.KJ4.RUN

theorem k_setup : kSetup kd = true := by quickRfl

theorem k_hdr : kHdr kd = true := by quickRfl

theorem k_pts : kPts kd = true := by quickRfl

theorem k_lam : kLam kd = true := by quickRfl

theorem k_chains : kChains kd = true := by quickRfl

theorem k_range : kRange kd = true := by quickRfl

theorem m_setup : mSetup md kd = true := by quickRfl

end CertificateChecks.KernelBounds.J4

end
