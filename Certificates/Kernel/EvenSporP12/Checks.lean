module

public import Certificates.Data.Kernel.EvenSporP12.Defs
public import Certificates.Kernel.EvenSporP12.K

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
theorem p12A_12 : p12A 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p12B_12 : p12B 12 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p12C_12 : p12C 12 = true := by
  decide +kernel

theorem p12K_12 : p12CheckK 12 = true := by
  rw [p12CheckK_eqB, p12CheckKB_eq, p12A_12, p12B_12, p12C_12]
  rfl

set_option maxHeartbeats 0 in
theorem p12A_13 : p12A 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p12B_13 : p12B 13 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem p12C_13 : p12C 13 = true := by
  decide +kernel

theorem p12K_13 : p12CheckK 13 = true := by
  rw [p12CheckK_eqB, p12CheckKB_eq, p12A_13, p12B_13, p12C_13]
  rfl

end CertificateChecks.KernelEvenSporP12
