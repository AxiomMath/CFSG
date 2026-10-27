module

public import Certificates.Kernel.E6RegPair.Checks
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CertificateChecks.KernelE6RegPair

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.KC.E6RegPair CFSG.KD.E6RegPair

theorem rows_check : ∀ ρ < 8, rowOK rows partners ρ = true := by
  intro ρ hρ
  interval_cases ρ
  · exact ch452150row0
  · exact ch452150row1
  · exact ch452150row2
  · exact ch452150row3
  · exact ch452150row4
  · exact ch452150row5
  · exact ch452150row6
  · exact ch452150row7

end CertificateChecks.KernelE6RegPair
