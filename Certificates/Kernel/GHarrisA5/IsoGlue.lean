module

public import Certificates.Kernel.GHarrisA5.Iso
public import CFSG.Certificates.Kernel.GHarrisA5Sound

public section

namespace CertificateChecks.KernelGHarrisA5

open CFSG.ComponentClassification.GHarris CFSG.KC.GHarrisA5

theorem iso_ok : ∀ j ∈ List.range 4,
    (∀ p q : alternatingGroup (Fin 5), GL42.phiA5 j (p * q) = (GL42.phiA5 j p).mul (GL42.phiA5 j q)) ∧
      KerOK j ∧ IntoOK j ∧ OntoOK j := by
  intro j hj
  rw [List.mem_range] at hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  exacts [⟨homOK_of_gen one_0 homGen_0 words_gen, ker_0, into_0, onto_0⟩,
    ⟨homOK_of_gen one_1 homGen_1 words_gen, ker_1, into_1, onto_1⟩,
    ⟨homOK_of_gen one_2 homGen_2 words_gen, ker_2, into_2, onto_2⟩,
    ⟨homOK_of_gen one_3 homGen_3 words_gen, ker_3, into_3, onto_3⟩]

end CertificateChecks.KernelGHarrisA5

end
