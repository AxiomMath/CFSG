
module

public import Certificates.Kernel.A45Cls.Cls
public import Certificates.Kernel.Parrott946.Cls
public import Certificates.Data.Kernel.A45Cls.Defs
public import Certificates.Data.Kernel.PermCent.CV
public import Certificates.Certificate946016Base

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KC.A45Cls CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.RankThree.GF2n.Parrott
  CertificateChecks.KernelA45

@[expose] noncomputable def elsA : List (Equiv.Perm (Fin 45)) :=
  [t, u, v, sigma1, sigma2, alpha1, beta1, alpha2, beta2, beta, o3b, o3c]

@[expose] noncomputable def elsP : List (Equiv.Perm (Fin 45)) :=
  [u, sigma1, sigma2, alpha1, beta1, alpha2, beta2, beta]

@[expose] noncomputable def pkL (L : List (Equiv.Perm (Fin 45))) (j : ℕ) : ℕ := (cOf (L.getD j 1)).1

theorem binds :
    K1.G 0 = KA.G 0 ∧ K1.G 1 = KA.G 1 ∧ K1.G 2 = KA.G 2 ∧
    K12.G 0 = KA.G 0 ∧ K12.G 1 = KA.G 1 ∧ K12.G 2 = KA.G 2 ∧
    K12i.G 0 = KA.G 0 ∧ K12i.G 1 = KA.G 1 ∧ K12i.G 2 = KA.G 2 ∧
    (cOf sigma1).1 = K1.T K1.r0 ∧ (cOf (sigma1 * sigma2)).1 = K12.T K12.r0 ∧
    (cOf (sigma1 * sigma2⁻¹)).1 = K12i.T K12i.r0 ∧ bindWs 45 6 3 KA.G CZ.G zW 0 = true := by
  decide +kernel

theorem words : bindWs 45 6 3 KA.G (pkL elsA) wA 0 = true ∧
    bindWs 45 6 2 KA.G (pkL elsP) wP 0 = true := by
  decide +kernel

theorem orders : K1.N = 80 ∧ K12.N = 240 ∧ K12i.N = 480 ∧ K1.ng = 3 ∧ K12.ng = 3 ∧ K12i.ng = 3 ∧
    CZ.N = 648 ∧ CZ.ng = 6 ∧ wA.length = 12 ∧ wP.length = 8 ∧ zW.length = 6 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ids : CZ.T 0 = pidn 45 6 := by decide +kernel

theorem fixes : fixK 45 6 (cOf t).1 = 13 ∧ fixK 45 6 (cOf u).1 = 13 ∧ fixK 45 6 (cOf v).1 = 7 := by
  decide +kernel

theorem cent : allN 6 (fun k => eq22 45 6 (mask 6) (CZ.G k) (K1.T K1.r0) (K1.T K1.r0) (CZ.G k)) =
    true := by
  decide +kernel

end CertificateChecks.Parrott946

end
