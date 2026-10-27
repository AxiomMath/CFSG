module

public import Certificates.Kernel.Misc.Perm.Bloom13A
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.Bloom13

open CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw
open CFSG.KC.Misc.Clos (allR allR_iff forall_of_chunks)

theorem chunk5 :
    allR (2187 * 5) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk6 :
    allR (2187 * 6) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk7 :
    allR (2187 * 7) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk8 :
    allR (2187 * 8) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl


end CertificateChecks.KernelMisc.Bloom13

end
