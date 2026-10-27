module

public import Certificates.Kernel.PropA.G5Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.Facts
public import Certificates.Kernel.PropA.KFacts

public section

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA

theorem pa450010_model (b : Bool) :
    Model (K28 b) D28 pT pa450010x ∧ Nat.card ↥(K28 b) = 380160 ∧
      ∀ y ∈ D28, orderOf y = 2 → Nat.card ↥(D28 ⊓ centralizer ({y} : Set (Perm (Fin 28)))) = 240 →
        ∃ a ∈ D28, a * y * a⁻¹ = pa450010x :=
  ⟨{ D_le := D28_le_K28 b
     card_J := pa450010_card_J
     card_Kx := pa450010_card_Kx b
     J_normal := pa450010_J_normal b
     J_center := pa450010_J_center
     card_Y := pa450010_card_Y b
     G3 := pa450010_G3 b
     G5 := pa450010_G5
     G1 := pa450010_G1 b
     G2 := pa450010_G2 b }, card_K28 b, pa450010_I3⟩

end CertificateChecks.KernelPropA
