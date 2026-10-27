module

public import Certificates.Data.Kernel.FongPerm
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalPermData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelFongPerm

open CFSG.KC.FongPerm CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

@[expose] def code12a : ℕ := 184726996899603491
@[expose] def code12b : ℕ := 365002956609719367
@[expose] def code23a : ℕ := 29396287020561317414859794500619265
@[expose] def code23b : ℕ := 4436007312844787929641103698034959
@[expose] def code24a : ℕ := 817395973838868159142633316802379971
@[expose] def code24b : ℕ := 938078705133617800621527216201835139

theorem ok40260_gen24 : checkK 24 code24a code24b m24_7_claims = true := by quickRfl

theorem ok40260_sec12 : secK 12 code12a code12b m12_5_claims = true := by quickRfl

theorem ok40260_sec23 : secK 23 code23a code23b m23_7_claims = true := by quickRfl

theorem ok40260_sec24 : secK 24 code24a code24b m24_5_claims = true := by quickRfl

end CertificateChecks.KernelFongPerm

end
