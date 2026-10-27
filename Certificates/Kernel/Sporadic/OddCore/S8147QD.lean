module

public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.LocalComp.BfsGen
public import CFSG.RankThree.Native.SuzFiveCheckInputs
meta import CFSG.RankThree.Native.SuzFiveCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.S8147

open CFSG.RankThree.Native CFSG.Monster.B.Mathieu

meta def qwM : Array Nat :=
  (CFSG.KC.BfsGen.search 1782 11 suzFiveQArrs).1.map fun t =>
    (((List.range 6).flatMap fun j => (List.range 5).map fun e => (j, e)).find? fun je =>
      powArr 1782 (suzFiveLineArr je.1) je.2 == t).elim 0 fun je => 8 * je.1 + je.2

end CertificateChecks.KernelSpor.S8147

#krows CertificateChecks.KernelSpor.SFQW CertificateChecks.KernelSpor.S8147.qwM

end
