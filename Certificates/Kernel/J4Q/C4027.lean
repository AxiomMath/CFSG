module

public import CFSG.Sporadic.J4.QT2LocX0CheckInputs
public import Certificates.Kernel.J4Q.C4027G
public import Certificates.Kernel.J4Q.C4027I
public import Certificates.Kernel.J4Q.C4027P

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.Sporadic.J4.QT2

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
theorem c4027 : chkX0All = true := by
  have hc : chkX0Conj = true := by
    unfold chkX0Conj
    rw [Bool.and_eq_true]
    exact ⟨x0ConjT_ok.1, x0ConjZ_ok.1⟩
  unfold chkX0All
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨gens_ok, x0Orb_ok.1⟩, hc⟩, x0invs_ok⟩, pts_ok⟩

end CertificateChecks.KernelJ4Q

end
