module

public import Certificates.Kernel.Fi23Five.Glue
public import Certificates.Data.Fi23FiveFix

public section

namespace CertificateChecks.KernelFi23Five

open CFSG.KD.Fi23K CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native


theorem fiveFix_ok : fi23FiveFixOK orbLit = true := by
  unfold fi23FiveFixOK
  dsimp only
  rw [path_eq, List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  by_cases hab : a + b = 0
  · simp [hab]
  · rw [fix_main (List.mem_range.1 ha) (List.mem_range.1 hb) hab, len_repL]
    simp

end CertificateChecks.KernelFi23Five

end
