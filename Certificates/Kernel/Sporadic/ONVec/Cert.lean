module

public import Certificates.Kernel.Sporadic.ONVec.CertSig
public import Certificates.Kernel.Sporadic.ONVec.CertStr

public section

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.F3.Native CFSG.ONSchreier.Native

variable (sigAll : ∀ s < 1023, sigS s = true) (ssortAll : ∀ s < 1023, ssortS s = true)

include sigAll ssortAll in
theorem vector_cert_ok : vectorCert (digitsW CFSG.ONSchreier.Data.rootDigits) CFSG.ONSchreier.Data.spanIdx
    (rowsOf 154 CFSG.ONSchreier.Data.spanInvPayload) (rowsOf 154 CFSG.ONSchreier.Data.formPayload)
    CFSG.ONSchreier.Data.baseList CFSG.ONSchreier.Data.strongWords 3 = true := by
  unfold vectorCert
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨orbit_ok, root_ok⟩, root_ne⟩, disc_ok⟩, basis_ok⟩, form_ok⟩, gram_ok⟩,
    by decide⟩, by decide⟩, sig_ok sigAll ssortAll⟩, strong_ok⟩

end CertificateChecks.KernelSpor.ONVec

end
