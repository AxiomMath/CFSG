module

public import Certificates.Kernel.E64CC.Orb

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE64CC

open CFSG.KC.E64CC

theorem cm0 : cmK CFSG.KD.E64CC.D MT.T MT.N 0 = true := by decide +kernel
theorem cm1 : cmK CFSG.KD.E64CC.D MT.T MT.N 1 = true := by decide +kernel
theorem cm2 : cmK CFSG.KD.E64CC.D MT.T MT.N 2 = true := by decide +kernel
theorem cm3 : cmK CFSG.KD.E64CC.D MT.T MT.N 3 = true := by decide +kernel
theorem cm4 : cmK CFSG.KD.E64CC.D MT.T MT.N 4 = true := by decide +kernel
theorem cm5 : cmK CFSG.KD.E64CC.D MT.T MT.N 5 = true := by decide +kernel
theorem cm6 : cmK CFSG.KD.E64CC.D MT.T MT.N 6 = true := by decide +kernel
theorem cm7 : cmK CFSG.KD.E64CC.D MT.T MT.N 7 = true := by decide +kernel
theorem cm8 : cmK CFSG.KD.E64CC.D MT.T MT.N 8 = true := by decide +kernel
theorem cm9 : cmK CFSG.KD.E64CC.D MT.T MT.N 9 = true := by decide +kernel
theorem cm10 : cmK CFSG.KD.E64CC.D MT.T MT.N 10 = true := by decide +kernel
theorem cm11 : cmK CFSG.KD.E64CC.D MT.T MT.N 11 = true := by decide +kernel
theorem cm12 : cmK CFSG.KD.E64CC.D MT.T MT.N 12 = true := by decide +kernel
theorem cm13 : cmK CFSG.KD.E64CC.D MT.T MT.N 13 = true := by decide +kernel

theorem cm_ok : ∀ k < 14, cmK CFSG.KD.E64CC.D MT.T MT.N k = true := by
  intro k hk
  interval_cases k
  exacts [cm0, cm1, cm2, cm3, cm4, cm5, cm6, cm7, cm8, cm9, cm10, cm11, cm12, cm13]

end CertificateChecks.KernelE64CC

end
