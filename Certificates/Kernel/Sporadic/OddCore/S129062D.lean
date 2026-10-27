module

public import Certificates.Kernel.Sporadic.OddCore.S2307D
public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzCheck
meta import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.SuzCheck
meta import Certificates.Kernel.Sporadic.OddCore.S2307D

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.S129C
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.suzColHex
#kmisc_hexflat CertificateChecks.KernelSpor.S129C
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.suzColHex 3 911 6 1

namespace CertificateChecks.KernelSpor.S129062

meta def idxM : Array Nat :=
  let E := CertificateChecks.KernelSpor.S2307.eM
  (List.range E.size).toArray.filter fun k => CFSG.Sporadic.SuzOddCore.isInvTab E[k]!

end CertificateChecks.KernelSpor.S129062

#krows32 CertificateChecks.KernelSpor.S129I CertificateChecks.KernelSpor.S129062.idxM

end
