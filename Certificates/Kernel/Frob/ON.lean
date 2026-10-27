module

public import Certificates.Data.Kernel.OpsFrob
public import Certificates.Kernel.LocalComp.F3.ON
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFrob.ON

open CFSG.KC.OpsFrob CFSG.SectionRank.Native

theorem frob_K : frobL CFSG.KD.LC.F3.ON.lay CFSG.KD.LC.F3.ON.A CFSG.KD.LC.F3.ON.B onFrobData =
    true := by quickRfl

end CertificateChecks.KernelFrob.ON

end
