module

public import Certificates.Kernel.E64CC.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE64CC

open CFSG.KC.E64CC CFSG.KC.Enum

theorem set0 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 0 i)) = true := by decide +kernel
theorem set1 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 35 i)) = true := by decide +kernel
theorem set2 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 70 i)) = true := by decide +kernel
theorem set3 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 105 i)) = true := by decide +kernel
theorem set4 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 140 i)) = true := by decide +kernel
theorem set5 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 175 i)) = true := by decide +kernel
theorem set6 : allN 35 (fun i => setK CFSG.KD.E64CC.D (Nat.add 210 i)) = true := by decide +kernel

end CertificateChecks.KernelE64CC

end
