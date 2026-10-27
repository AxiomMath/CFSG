module

public import CFSG.RankThree.Native.ONTripleMatSound
public import Certificates.Kernel.Misc.ON.Rels
public import Certificates.Kernel.Misc.ON.RegsAll
public import Certificates.Kernel.Misc.ON.Local

@[expose] public section

namespace CertificateChecks.KernelMisc.ON

open CFSG.RankThree.Native.ONTriple CFSG.KC.Misc.F7

theorem regOKK : RegOK := mrep_regM gensB regsB

theorem pivK : ∀ t < 60, pivOK (ptM t) (pvM t) = true := (chkPtsM_spec ptsB).1

end CertificateChecks.KernelMisc.ON
