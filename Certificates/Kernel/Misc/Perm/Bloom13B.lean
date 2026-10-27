module

public import Certificates.Kernel.Misc.Perm.Bloom13A
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.Bloom13

open CFSG.RankThree.PartTwo.Toolkit CFSG.RankThree.PartTwo.Toolkit.Raw
open CFSG.KC.Misc.Clos (allR allR_iff forall_of_chunks)

theorem chunk0 :
    allR (2187 * 0) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk1 :
    allR (2187 * 1) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk2 :
    allR (2187 * 2) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk3 :
    allR (2187 * 3) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl

theorem chunk4 :
    allR (2187 * 4) 2187 (bloom13At 2466 f0Lit nfLit coverLit) = true := by quickRfl


end CertificateChecks.KernelMisc.Bloom13

end
