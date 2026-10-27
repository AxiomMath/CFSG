module

public import Certificates.Kernel.E6TwA2.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelE6TwA2

open Certificates.E6TwA2K

set_option maxRecDepth 100000

theorem ch214102_roots : rootsOK RP rootsC = true := by quickRfl

theorem ch214102_recs0 : recsOK RP cr0 = true := by quickRfl
theorem ch214102_recs1 : recsOK RP cr1 = true := by quickRfl
theorem ch214102_recs2 : recsOK RP cr2 = true := by quickRfl
theorem ch214102_recs3 : recsOK RP cr3 = true := by quickRfl
theorem ch214102_recs4 : recsOK RP cr4 = true := by quickRfl

theorem ch214102_rep0 : repOK 1 cr0 = true := by quickRfl
theorem ch214102_rep1 : repOK 2 cr1 = true := by quickRfl
theorem ch214102_rep2 : repOK 3 cr2 = true := by quickRfl
theorem ch214102_rep3 : repOK 9 cr3 = true := by quickRfl
theorem ch214102_rep4 : repOK 14 cr4 = true := by quickRfl

theorem ch214102_words : wordsOK reps wd = true := by quickRfl
theorem ch214102_reps : (reps == [0, 1, 2, 3, 4, 8, 13, 27]) = true := by decide +kernel

theorem ch214102_norm : normOK 729 = true := by quickRfl

end CertificateChecks.KernelE6TwA2

end
