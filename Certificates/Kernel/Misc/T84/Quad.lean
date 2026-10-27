module

public import Certificates.Data.Kernel.Misc.T84QuadK
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelT84Q

open CFSG.KC.Misc.GL4 CFSG.KC.Misc.T84 CFSG.KC.Misc.T84Q

theorem ch442350_b : q442350B S0L = true := by quickRfl

theorem ch442350_t : q442350T S0L = true := by quickRfl

theorem ch442350_f : q442350F S0L = true := by quickRfl

end CertificateChecks.KernelT84Q
