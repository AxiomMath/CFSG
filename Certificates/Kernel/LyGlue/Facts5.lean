module

public import Certificates.Kernel.LyY.Card
public import Certificates.Kernel.LyGlue.Facts2

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv Subgroup
  CFSG.Sporadic.Recognition CFSG.Certificates.Kernel.PkCV CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier

theorem exists_Phiy (hM : Ly0.ModelChecks) (hY : Ly1080.YOK)
    (hcY : Nat.card Ly0.Y0 ≤ 349920) :
    ∃ Φy : ↥Ly0.UYperm ≃* ↥Ly1080.Y0,
      (∀ k (hk : k < 4) (hmem : Ly0.uG k ∈ Ly0.UYperm),
        (Φy ⟨Ly0.uG k, hmem⟩ : Perm (Fin 1080)) = Ly1080.ug k) ∧
      (∀ (x : Perm (Fin Ly0.deg)) (hx : x ∈ Ly0.UYperm), ∀ a ∈ OY,
        x a ∈ OY ∧ fY (x a) = (Φy ⟨x, hx⟩ : Perm (Fin 1080)) (fY a)) ∧
      Nat.card ↥Ly0.UYperm = 349920 := by
  obtain ⟨φ, hsurj, hgen, hcomp⟩ := exists_phiY hM.tab hY
  have eG : Ly0.UYperm = closure (Ly0.uG '' {k | k < 4}) := Glue.UYperm_eq
  have eH : closure (Ly1080.ug '' {k | k < 4}) = Ly1080.Y0 :=
    le_antisymm ((closure_le _).2 (by rintro _ ⟨k, hk, rfl⟩; exact Ly1080.ug_mem hY hk))
      (Glue.Y0_le_closure1080 hY)
  have hcU : Nat.card ↥Ly0.UYperm ≤ 349920 := by
    have h1 : Nat.card ↥Ly0.UYperm = Nat.card ↥(Ly0.UYperm.subgroupOf Ly0.B0) :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Ly0.UYperm_le_B0).toEquiv).symm
    rw [h1]
    exact (Subgroup.card_le_of_le (Ly0.UY_le_Y0 hM.tab hM.struct hM.cp1 hM.inv)).trans hcY
  have hcG : Nat.card ↥(closure (Ly0.uG '' {k | k < 4})) ≤ 349920 := by rw [← eG]; exact hcU
  have hle1 := Nat.card_le_card_of_surjective φ hsurj
  have hge : 349920 ≤ Nat.card ↥(closure (Ly1080.ug '' {k | k < 4})) := by
    rw [eH, CertificateChecks.KernelLyY.card_Y0]
  have hbij : Function.Bijective φ := hsurj.bijective_of_nat_card_le (by omega)
  refine ⟨(MulEquiv.subgroupCongr eG).trans ((MulEquiv.ofBijective φ hbij).trans
    (MulEquiv.subgroupCongr eH)), fun k hk hmem => hgen k hk, fun x hx a ha => ?_, ?_⟩
  · exact hcomp ⟨x, eG ▸ hx⟩ a ha
  · have : Nat.card ↥Ly0.UYperm = Nat.card ↥(closure (Ly0.uG '' {k | k < 4})) := by rw [eG]
    omega

end CertificateChecks.KernelLy

end
