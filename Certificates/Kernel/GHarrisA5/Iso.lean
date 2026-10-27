module

public import Certificates.Data.Kernel.GHarrisA5Gen

public section

namespace CertificateChecks.KernelGHarrisA5

open CFSG.ComponentClassification.GHarris CFSG.KC.GHarrisA5

abbrev KerOK (j : ℕ) : Prop :=
  ∀ p : alternatingGroup (Fin 5), GL42.phiA5 j p = GL42.M4c.one → p = 1

abbrev IntoOK (j : ℕ) : Prop := ∀ p : alternatingGroup (Fin 5), GL42.phiA5 j p ∈ GL42.a5At j

abbrev OntoOK (j : ℕ) : Prop := ∀ c ∈ GL42.a5At j, ∃ p : alternatingGroup (Fin 5), GL42.phiA5 j p = c

theorem words_gen : WordsGen := by decide +kernel

theorem one_0 : GL42.phiA5 0 1 = GL42.M4c.one := by decide +kernel
theorem one_1 : GL42.phiA5 1 1 = GL42.M4c.one := by decide +kernel
theorem one_2 : GL42.phiA5 2 1 = GL42.M4c.one := by decide +kernel
theorem one_3 : GL42.phiA5 3 1 = GL42.M4c.one := by decide +kernel

theorem homGen_0 : HomGen 0 := by decide +kernel
theorem homGen_1 : HomGen 1 := by decide +kernel
theorem homGen_2 : HomGen 2 := by decide +kernel
theorem homGen_3 : HomGen 3 := by decide +kernel

theorem ker_0 : KerOK 0 := by decide +kernel
theorem ker_1 : KerOK 1 := by decide +kernel
theorem ker_2 : KerOK 2 := by decide +kernel
theorem ker_3 : KerOK 3 := by decide +kernel

theorem into_0 : IntoOK 0 := by decide +kernel
theorem into_1 : IntoOK 1 := by decide +kernel
theorem into_2 : IntoOK 2 := by decide +kernel
theorem into_3 : IntoOK 3 := by decide +kernel

theorem onto_0 : OntoOK 0 := by decide +kernel
theorem onto_1 : OntoOK 1 := by decide +kernel
theorem onto_2 : OntoOK 2 := by decide +kernel
theorem onto_3 : OntoOK 3 := by decide +kernel

end CertificateChecks.KernelGHarrisA5

end
