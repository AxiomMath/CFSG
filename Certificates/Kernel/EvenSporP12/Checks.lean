module

public import Certificates.Data.Kernel.EvenSporP12.Defs

public section

namespace CertificateChecks.KernelEvenSporP12

open CFSG.EvenSporadicStandard.M12Std.SolomonK.P12 CFSG.KC.EvenSporP12

@[expose] def entsB (as : List (Array Nat)) : Bool := as.all fun a => a.toList.all (· < 16)

theorem ents12 : entsB (pGenSw.map (swapsArr 12)) && entsB (eGenSw.map (swapsArr 12)) &&
    entsB (cGenSw.map (swapsArr 12)) = true := by
  decide +kernel

theorem ents13 : entsB (pGenSw.map (swapsArr 13)) && entsB (eGenSw.map (swapsArr 13)) &&
    entsB (cGenSw.map (swapsArr 13)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p12K_12 : p12CheckK 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p12K_13 : p12CheckK 13 = true := by
  decide +kernel

end CertificateChecks.KernelEvenSporP12
