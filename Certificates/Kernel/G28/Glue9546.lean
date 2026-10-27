module

public import Certificates.Data.Item434G28
import CFSG.Certificates.Kernel.G28.T3Sound
import Certificates.Kernel.G28.T39546

public section

namespace Certificates.Kernel.G28

open CFSG.KC.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem t3Checks9546 : t3OK t3L = true ∧ goodPair uCode zCode = true ∧
    conjOK t3L e0L conjG conjGi = true := by
  have h := t39546
  rw [← codeP_wordCode, ← codeP_wordCode, ← codeP_wordCode] at h
  exact t3_of (valid_wordCode _) (valid_wordCode _) (valid_wordCode _) h

end Certificates.Kernel.G28

end
