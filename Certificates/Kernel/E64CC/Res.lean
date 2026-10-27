module

public import Certificates.Kernel.E64CC.Orb

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE64CC

open CFSG.KC.E64CC CFSG.KC.Enum

theorem res0 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 1 i)) = true := by
  decide +kernel
theorem res1 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 102 i)) = true := by
  decide +kernel
theorem res2 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 203 i)) = true := by
  decide +kernel
theorem res3 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 304 i)) = true := by
  decide +kernel
theorem res4 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 405 i)) = true := by
  decide +kernel
theorem res5 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 506 i)) = true := by
  decide +kernel
theorem res6 : allN 101 (fun i => resK CFSG.KD.E64CC.D MT.T (Nat.add 607 i)) = true := by
  decide +kernel

end CertificateChecks.KernelE64CC

end
