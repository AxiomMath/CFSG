module

public import Certificates.Data.Item434G28
public import Certificates.Data.Kernel.G28.Defs
import CFSG.Certificates.Kernel.G28.Sound
import Certificates.Kernel.G28.Gen9547

public section

namespace Certificates.Kernel.G28

open CFSG.KC.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem codeP_uCode : codeP uCode = powP (wordP u9W) 3 := by
  rw [uCode, u9Code, codeP_powCode (valid_wordCode _), codeP_wordCode]

theorem codeP_zCode : codeP zCode = powP (wordP z9W) 3 := by
  rw [zCode, z9Code, codeP_powCode (valid_wordCode _), codeP_wordCode]

theorem genOK9547 : genOK uCode zCode genW targetN targetSteps = true := by
  have h := gen9547
  rw [← codeP_uCode, ← codeP_zCode] at h
  exact genOK_of (valid_powCode (valid_wordCode _) 3) (valid_powCode (valid_wordCode _) 3) h

end Certificates.Kernel.G28

end
