module

public import Certificates.Kernel.E64CC.Data

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelE64CC

open CFSG.KC.E64CC CFSG.KC.Enum

@[expose] noncomputable def tripRow (k₁ : Nat) : Bool :=
  allN 14 fun k₂ => allN 14 fun k₃ => tripK CFSG.KD.E64CC.D k₁ k₂ k₃

theorem trip0 : tripRow 0 = true := by decide +kernel
theorem trip1 : tripRow 1 = true := by decide +kernel
theorem trip2 : tripRow 2 = true := by decide +kernel
theorem trip3 : tripRow 3 = true := by decide +kernel
theorem trip4 : tripRow 4 = true := by decide +kernel
theorem trip5 : tripRow 5 = true := by decide +kernel
theorem trip6 : tripRow 6 = true := by decide +kernel
theorem trip7 : tripRow 7 = true := by decide +kernel
theorem trip8 : tripRow 8 = true := by decide +kernel
theorem trip9 : tripRow 9 = true := by decide +kernel
theorem trip10 : tripRow 10 = true := by decide +kernel
theorem trip11 : tripRow 11 = true := by decide +kernel
theorem trip12 : tripRow 12 = true := by decide +kernel
theorem trip13 : tripRow 13 = true := by decide +kernel

theorem trip_ok : ∀ k₁ < 14, tripRow k₁ = true := by
  intro k hk
  interval_cases k
  exacts [trip0, trip1, trip2, trip3, trip4, trip5, trip6, trip7, trip8, trip9, trip10, trip11,
    trip12, trip13]

end CertificateChecks.KernelE64CC

end
