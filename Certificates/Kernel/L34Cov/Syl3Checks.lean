module

public import Certificates.Kernel.L34Cov.LiftNormChecks
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4WitCertInputs

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W
open CFSG.ComponentClassification.GrSLit.GrS4
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def wK (w : List Nat) : Nat := pword (gS GT) w (pidn 42 6)

@[expose] noncomputable def zK (k : Nat) : Nat :=
  pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (CertificateChecks.KernelLC.L34PR.YI k) (GT 5))
    (CertificateChecks.KernelLC.L34PR.Y k)

@[expose] noncomputable def nnK (k : Nat) : Bool :=
  notB (allN 4 fun i => notB (allN 64 fun q =>
    notB (Nat.beq (CertificateChecks.KernelLC.L34PT.T q)
      (cjK (zK k) (CertificateChecks.KernelLC.L34PT.G i)))))

@[expose] noncomputable def witX (k x xi : Nat) : Bool :=
  andB (Nat.beq (pcomp 42 6 (mask 6) x (GT 5)) (pcomp 42 6 (mask 6) (GT 5) x))
    (andB (canonK 42 6 (mask 6) (42 * 6) xi)
      (andB (Nat.beq (pcomp 42 6 (mask 6) x xi) (pidn 42 6))
        (memK 192 CertificateChecks.KernelLC.L34PB.T
          (pcomp 42 6 (mask 6) xi (CertificateChecks.KernelLC.L34PR.Y k)))))

@[expose] noncomputable def witK (k : Nat) (e : Nat × List Nat) : Bool :=
  andB (Nat.beq e.1 k) (witX k (wK e.2) (pinvS 42 6 (mask 6) (wK e.2)))

theorem ch22900s_k : allN 105 (fun k => orB (nnK k) (syl3Wit.any (witK k))) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
