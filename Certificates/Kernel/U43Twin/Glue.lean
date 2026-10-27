module

public import Certificates.Kernel.U43Twin.SFacts

public section

namespace CertificateChecks.KernelU43Twin

open Certificates.U43Twin

theorem allOK_true : allOK () = true := by
  unfold allOK
  simp only [t0OK_true, qOK_true, orbOK_true, cOK_true, tOK_true, candsOK_true, invOK_true,
    q8OK_true, permOK_true, oddOK_true, psiOK_true, centOK_true, commOK_true, Bool.and_self]

end CertificateChecks.KernelU43Twin

end
