module

public import Certificates.Kernel.LocalComp.L34Para.Chk
public import Certificates.Kernel.L34W.Gens

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W
open CFSG.KLie.CT (andB notB)

@[expose] noncomputable def cjK (g x : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) g x) g

theorem ch22212n_k : allN 64 (fun k => andB (memK 64 CertificateChecks.KernelLC.L34PT.T
    (cjK (GT 4) (tgK GT k))) (memK 64 CertificateChecks.KernelLC.L34PT.T (cjK (GT 5) (tgK GT k)))) =
    true := by
  decide +kernel

theorem ch22212n_c : Nat.beq (pcomp 42 6 (mask 6) (GT 4) (GT 5)) (pcomp 42 6 (mask 6) (GT 5) (GT 4)) =
    true := by
  decide +kernel

theorem ch22212n_neg : notB (memK 64 CertificateChecks.KernelLC.L34PT.T (cjK (GT 0) (tgK GT 1))) =
    true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
