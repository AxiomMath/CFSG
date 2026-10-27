module

public import CFSG.LocalAnalysis.OddStandard.ONanIdCertInputs
public import Certificates.Kernel.L34W.Gens
public import Certificates.Kernel.LocalComp.L34Para.Data

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.L34W
open CertificateChecks.KernelLC.L34Para CertificateChecks.KernelL34W
open CFSG.OddStandard.ONanRec.IdCert
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def mulK (x y : Nat) : Nat := pcomp 42 6 (mask 6) x y

@[expose] noncomputable def comK (x y : Nat) : Bool := Nat.beq (mulK x y) (mulK y x)

@[expose] noncomputable def tK (m : Nat) : Nat := tgK GT m

@[expose] noncomputable def vK (j : Nat) : Nat :=
  nIf(Nat.beq j 0, GT 4, nIf(Nat.beq j 1, GT 5, mulK (GT 4) (GT 5)))

@[expose] noncomputable def q8K (p m₁ m₂ : Nat) : Bool :=
  andB (comK (tK m₁) p) (andB (comK (tK m₂) p) (andB (notB (Nat.beq (mulK (tK m₁) (tK m₁))
    (pidn 42 6))) (andB (Nat.beq (mulK (tK m₁) (tK m₁)) (mulK (tK m₂) (tK m₂)))
      (notB (comK (tK m₁) (tK m₂))))))

@[expose] noncomputable def cK (p : Nat) : List Nat := (List.range 64).filter fun m => comK (tK m) p

@[expose] noncomputable def sigK (p : Nat) : Bool :=
  orB (notB (Nat.beq (mulK p p) (pidn 42 6)))
    (orB ((List.range 64).any fun m => Nat.beq (mulK (tK m) p) (mulK (vK 2) (tK m)))
      (notB ((cK p).any fun m₁ => (cK p).any fun m₂ => q8K p m₁ m₂)))

@[expose] noncomputable def centK : Bool :=
  aCent.all fun d => (List.range 64).all fun m => comK (tK m) (tK d.1) == d.2.contains m

theorem ch6147c_k : centK = true := by decide +kernel

theorem ch6147s_k : allN 64 (fun k => allN 3 fun j => sigK (mulK (tK k) (vK j))) = true := by
  decide +kernel

end CertificateChecks.KernelL34Cov

end
