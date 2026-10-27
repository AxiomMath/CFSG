module

public import Certificates.Data.Kernel.G23Code.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelG23C

open CFSG.KD.G23C CFSG.KC.Ord CFSG.KD.LocLn CFSG.GH74.QTGen4.Recog.G23

theorem consts_ok : constsChk = true := by quickRfl

theorem inv_ok0 : invChk 0 = true := by quickRfl
theorem inv_ok1 : invChk 1 = true := by quickRfl
theorem inv_ok2 : invChk 2 = true := by quickRfl
theorem inv_ok3 : invChk 3 = true := by quickRfl
theorem inv_ok4 : invChk 4 = true := by quickRfl
theorem inv_ok5 : invChk 5 = true := by quickRfl

theorem words_ok : wordsChk g23Words = true := by quickRfl

end CertificateChecks.KernelG23C

end
