module

public import Certificates.Kernel.HMathieu.Odd
public import Certificates.Data.Kernel.HMathieu.PickJ

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.Odd

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def okH24 (a : Array Nat) : Bool :=
  (conj3A24.any fun h => conjToB h a s0Arr && inAutOK h) || rankOK 11 7 (matOf 11 (actC11 a))

set_option maxHeartbeats 0 in
theorem h24 : tailOK okH24 κCCols liftCCols 11 (E.getD 5 []) = true := by decide +kernel

end CertificateChecks.KernelHMathieu.Odd

end
