module

public import Certificates.Data.Kernel.E6RegPair
public import Certificates.Kernel.E6RegPair.Data
import all Certificates.Data.Kernel.E6RegPair
import all CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
import all CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeChar
import CFSG.Certificates.Kernel.Common.EachTrue

public section

open CFSG.KC.E6RegPair CFSG.KD.E6RegPair

#kc_each CertificateChecks.KernelE6RegPair ch452150row (fun ρ => rowOK rows partners ρ) 0 8

namespace CertificateChecks.KernelE6RegPair

set_option maxHeartbeats 0 in
theorem partners_check : partnersOK partners = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem stab_check : stabOK stab = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem orbit7_check : orbit7OK () = true := by
  decide +kernel

end CertificateChecks.KernelE6RegPair
