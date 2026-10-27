module

public import Certificates.Kernel.He7222.GWords
public import Certificates.Kernel.He7223.GlueFinal

public section

namespace CFSG.KD.He7222

open CFSG.Quasithin.KGC31.He CertificateChecks.KernelHe7223

theorem R5_eq : R5 = w5W := by
  rw [w5W_eq, eW_eq]
  decide +kernel

theorem R7_eq : R7 = w7W := by
  rw [w7W_eq, qW_eq]
  decide +kernel

end CFSG.KD.He7222

end
