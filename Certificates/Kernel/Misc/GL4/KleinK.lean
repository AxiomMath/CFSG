module

public import Certificates.Data.Kernel.Misc.GL4Klein

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.GL4A5

open CFSG.KC.Misc.GL4

theorem kleinNC : KleinNC := by decide +kernel

theorem kleinOC : KleinOC := by decide +kernel

end CertificateChecks.KernelMisc.GL4A5

end
