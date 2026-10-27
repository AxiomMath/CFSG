module

public import CFSG.RankThree.Native.ONTripleModelInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.RankThree.Native.ONTriplePresInputs

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple

theorem gensB : chkGensM = true := by quickRfl

theorem nontrivB : chkNontrivM = true := by quickRfl

theorem relsA : ∀ j < 12, relOKM ((coverRels 1 1 1).getD j []) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem relsM : ∀ j, 12 ≤ j → j < 24 → relOKM ((coverRels 1 1 1).getD j []) = true := by
  intro j h1 h2
  interval_cases j <;> quickRfl

theorem relsC : ∀ j, 24 ≤ j → j < 37 → relOKM ((coverRels 1 1 1).getD j []) = true := by
  intro j h1 h2
  interval_cases j <;> quickRfl

theorem relsB : ∀ j < 37, relOKM ((coverRels 1 1 1).getD j []) = true := by
  intro j hj
  by_cases c0 : j < 12
  · exact relsA j c0
  by_cases c1 : j < 24
  · exact relsM j (by omega) c1
  exact relsC j (by omega) hj

end CertificateChecks.KernelMisc.ON

end
