module

public import CFSG.Certificates.Kernel.PermCent.Sz8DSound
public import Certificates.Kernel.PermCent.K5129
public import Certificates.Certificate5128

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5129

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.Sz8
  CFSG.GH74.KGroups.Sz8D

theorem QS_ok_k : ValidSchreier QS := QS_valid_of kQS.1

theorem S_fix_k : ∀ s ∈ QS.originalSubgroup, s cpt = cpt := S_fix_of QS_ok_k kOrb.1

theorem fix_unique_k : ∀ i : Fin 65, (∀ s ∈ QS.originalSubgroup, s i = i) → i = cpt :=
  fix_unique_of QS_ok_k kOrb.1

theorem ys_k : ∀ j, ys j ∈ QS.originalSubgroup ⊓
    Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))) :=
  ys_mem_of QS_ok_k kSift.2 kCent.1

theorem ys0_k : ys 0 ≠ 1 := ys0_ne_of kYs

theorem hfin_k (κ : Equiv.Perm (Fin 65) → Equiv.Perm (Fin 65) → ZMod 2)
    (h1 : ∀ x ∈ QS.originalSubgroup, ∀ x' ∈ QS.originalSubgroup,
      ∀ y ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
        κ (x * x') y = κ x y + κ x' y)
    (h2 : ∀ x ∈ QS.originalSubgroup,
      ∀ y ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
      ∀ y' ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
        κ x (y * y') = κ x y + κ x y')
    (h3 : ∀ w ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
      ∀ y ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))), κ w y = 0)
    (h5 : ∀ x ∈ QS.originalSubgroup, κ x (x ^ 2) = 0)
    (h4t : ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
        κ (tt * s * tt⁻¹) (tt * t * tt⁻¹) = κ s t)
    (σ : Equiv.Perm (Fin 65)) (hσA : σ ∈ QA.originalSubgroup) (hσfix : σ cpt = cpt)
    (hσP : σ ∉ QP.originalSubgroup)
    (h4σ : ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))),
        κ (σ * s * σ⁻¹) (σ * t * σ⁻¹) = κ s t) :
    ∀ s ∈ QS.originalSubgroup,
      ∀ t ∈ QS.originalSubgroup ⊓
        Subgroup.centralizer (QS.originalSubgroup : Set (Equiv.Perm (Fin 65))), κ s t = 0 :=
  hfin_of QP_ok QP_valid.2 QA_ok QA_valid.2 norm_ok kQS.1 kQS.2 kSift.1 kSift.2 kSyP kOrb.1
    kOrb.2 kCent.1 kCent.2 kNc kDec kTt.1 kTt.2.1 kTt.2.2.1 kTt.2.2.2.1 kTt.2.2.2.2 kSig
    kConj.1 kConj.2 kSq kAlg κ h1 h2 h3 h5 h4t σ hσA hσfix hσP h4σ

end CFSG.Certificates.Kernel.PkCV.KGrp.K5129

end
