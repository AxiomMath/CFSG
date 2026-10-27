module

public import Certificates.Data.Kernel.LyI301.Defs
import Certificates.Kernel.LyI301.Checks
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KC.LyI301

theorem ly810304rows : ∀ r < 12, lyRow r = true := by
  intro r hr
  interval_cases r
  · exact ly810304row0
  · exact ly810304row1
  · exact ly810304row2
  · exact ly810304row3
  · exact ly810304row4
  · exact ly810304row5
  · exact ly810304row6
  · exact ly810304row7
  · exact ly810304row8
  · exact ly810304row9
  · exact ly810304row10
  · exact ly810304row11

end CFSG.KC.LyI301

end
