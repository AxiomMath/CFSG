module

public import Certificates.Kernel.McLThree.Wit
public import Certificates.Data.Kernel.McLThree.Defs
public import CFSG.Sporadic.SmallOddCore.McLIndexThreeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLThree

open CFSG.KS.McLThree CFSG.Sporadic.SmallOddCore

theorem chk : mcl3K McLCT.F MUE.G mclIndexNineUWords McL3W.A McL3W.B McL3W.C 1
    mclIndexThreeP0Words (mclIndexThreeMoverWords.getD 0 []) (mclIndexThreeMoverWords.getD 1 [])
    mclIndexThreeA mclIndexThreeG = true := by
  quickRfl

end CertificateChecks.KernelSpor.McLThree

end
