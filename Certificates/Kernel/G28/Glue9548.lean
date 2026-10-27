module

public import Certificates.Data.Item434G28Cent
import CFSG.Certificates.Kernel.G28.CentSound
import Certificates.Kernel.G28.Glue9547
import Certificates.Kernel.G28.Cent9548

public section

namespace Certificates.Kernel.G28

open CFSG.KC.G28 CFSG.RankThree.PartTwo.Sec4.Item434G28

theorem centOK9548 : centOK e0L centV0 centB centBinv = true := by
  have h := cent9548
  rw [← codeP_uCode, ← codeP_zCode] at h
  exact centOK_of (valid_powCode (valid_wordCode _) 3) (valid_powCode (valid_wordCode _) 3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) h

end Certificates.Kernel.G28

end
