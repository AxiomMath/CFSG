module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0SuzTests
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelLC.SuzB0Q CFSG.ComponentClassification.AS81.SuzB0.qText

#kmisc_hexflat CertificateChecks.KernelLC.SuzB0Q CFSG.ComponentClassification.AS81.SuzB0.qText
  3 1782 11 6

#kmisc_packarrs CertificateChecks.KernelLC.SuzB0QP CFSG.ComponentClassification.AS81.SuzB0.qProds 11

#kmisc_packarrs CertificateChecks.KernelLC.SuzB0QE CFSG.ComponentClassification.AS81.SuzB0.qElts 11

namespace CertificateChecks.KernelLC.B0Suz

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.KS.Raw

theorem q_eq {i : Nat} (hi : i < 6) : qArr i = unpack 1782 11 (SuzB0Q.F i) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound SuzB0Q.all i hi
  rw [← SuzB0Q.eq] at h
  exact h

end CertificateChecks.KernelLC.B0Suz

end
