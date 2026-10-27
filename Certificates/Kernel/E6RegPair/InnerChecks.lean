module

public import Certificates.Data.Kernel.E6RegInner
public import Certificates.Kernel.E6RegPair.Data
import all Certificates.Data.Kernel.E6RegInner
import all Certificates.Data.Kernel.E6RegPair
import all Certificates.Data.E6DiagRegularLines
import all Certificates.Data.E6DiagRegular
import all CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
import all CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar

public section

open CFSG.KC.E6RegInner CFSG.KD.E6RegPair

namespace CertificateChecks.KernelE6RegPair

set_option maxHeartbeats 0 in
theorem inner_check : innerOK stab = true := by
  decide +kernel

end CertificateChecks.KernelE6RegPair
