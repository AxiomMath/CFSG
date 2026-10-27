module

public import Certificates.Kernel.HeDc.Final
public import CFSG.Quasithin.H13.LocDblOdd
public import CFSG.Quasithin.H13.OverSylowDc
import CFSG.Blueprint.NativeSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListMain
public import Certificates.Data.DcRows

public section

namespace CFSG.KD.He7030

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H13.LocDbl CFSG.KD.HeDc
open CFSG.QuasithinUnique.Vol2Native.A312L (exists_conj_of_isSylowTwoOf)
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sq_138240 : ((138240 : ℕ).primeFactors.filter fun r => r ^ 2 ∣ 138240).card ≤ 2 := by
  simp [Nat.primeFactors]
  decide

theorem sq_21504 : ((21504 : ℕ).primeFactors.filter fun r => r ^ 2 ∣ 21504).card ≤ 2 := by
  simp [Nat.primeFactors]
  decide

theorem oddIndexBound_of_sylow {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS : IsSylowTwoOf S ⊤)
    (h : ∀ Y : Subgroup Γ, S ≤ Y → Y ≠ ⊤ → Nat.card Y ∣ 138240 ∨ Nat.card Y ∣ 21504) :
    OddIndexBound Γ [138240, 138240, 21504] := by
  intro Y hY hne
  obtain ⟨R, hR, hRY⟩ := exists_isSylowTwoOf_le_of_odd_index hY
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hS hR
  set e : Γ ≃* Γ := MulAut.conj g with he
  have hY' : Y.map e.symm.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    have := congrArg (Subgroup.map e.toMonoidHom) htop
    rwa [map_map_symm_self, Subgroup.map_top_of_surjective _ e.surjective] at this
  have hSY : S ≤ Y.map e.symm.toMonoidHom := by
    rw [← map_symm_map_self e S]
    refine Subgroup.map_mono ?_
    rw [show S.map e.toMonoidHom = R from hg]
    exact hRY
  have hc : Nat.card (Y.map e.symm.toMonoidHom) = Nat.card Y :=
    Subgroup.card_map_of_injective e.symm.injective
  rcases h _ hSY hY' with h | h
  · exact ⟨138240, by simp, hc ▸ h⟩
  · exact ⟨21504, by simp, hc ▸ h⟩

theorem card_of_le {Y : Subgroup CFSG.Sporadic.He.J} (hSY : heCtxK.S ≤ Y) (hY : Y ≠ ⊤) :
    ∃ j < 11, Nat.card Y = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024 := by
  obtain ⟨j, -, rfl⟩ := heK_complete Y hSY
  unfold memberOrTop at hY ⊢
  by_cases h : j < 11
  · rw [if_pos h]
    exact ⟨j, h, heK_member_card j h⟩
  · rw [if_neg h] at hY
    exact absurd rfl hY

theorem dvd_of_le {Y : Subgroup CFSG.Sporadic.He.J} (hSY : heCtxK.S ≤ Y) (hY : Y ≠ ⊤) :
    Nat.card Y ∣ 138240 ∨ Nat.card Y ∣ 21504 := by
  obtain ⟨j, hj, hc⟩ := card_of_le hSY hY
  rw [hc]
  interval_cases j <;> decide

theorem nine_of_le {Y : Subgroup CFSG.Sporadic.He.J} (hSY : heCtxK.S ≤ Y) (hY : Y ≠ ⊤)
    (h5 : 5 ∣ Nat.card Y) : 9 ∣ Nat.card Y := by
  obtain ⟨j, hj, hc⟩ := card_of_le hSY hY
  rw [hc] at h5 ⊢
  interval_cases j <;> revert h5 <;> decide

theorem sylowNoDouble_He_groupK : SylowNoDouble ↥CFSG.Sporadic.He.J := by
  refine sylowNoDouble_of_sylow heK_S_sylow fun Y hSY hY => ?_
  rcases dvd_of_le hSY hY with h | h
  · exact noIsoDouble_of_card_dvd (N := 138240) (by norm_num) h sq_138240
  · exact noIsoDouble_of_card_dvd (N := 21504) (by norm_num) h sq_21504

theorem oddIndexBound_He_groupK : OddIndexBound ↥CFSG.Sporadic.He.J [138240, 138240, 21504] :=
  oddIndexBound_of_sylow heK_S_sylow fun _ hSY hY => dvd_of_le hSY hY

theorem overSylow_JK : ∀ X S : Subgroup CFSG.Sporadic.He.J, Nat.card S = 2 ^ 10 → S ≤ X →
    5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X → False :=
  no_overgroup_of_sylow (R := heCtxK.S) (by rw [heK_card_S]; norm_num) (by rw [he_card]; norm_num)
    (by rw [he_card]; norm_num) fun _ hSX hX h5 h9 => h9 (nine_of_le hSX hX h5)

end CFSG.KD.He7030

end
