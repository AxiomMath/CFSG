module

public import CFSG.Certificates.Kernel.Hall82K.EnumSound
public import Certificates.Kernel.Hall82K.Enum
public import Certificates.Kernel.Hall82K.PermK
public import Certificates.Kernel.Hall82K.MGens
public import CFSG.CGT.Hall82.ModelFacts

public section

namespace CFSG.KD.Hall82E

open CFSG.KC.Hall82K CFSG.KC.Misc.Clos CFSG.CGT.Hall82
open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HeSylow

theorem enumM_all : ∀ k < 2160, enumAt 4439643498 34633937090 2160 EM PM SM CM k = true := by
  intro k hk
  have h0 := (allR_iff _ _ _).1 ch840001enM0 k
  have h1 := (allR_iff _ _ _).1 ch840001enM1 k
  have h2 := (allR_iff _ _ _).1 ch840001enM2 k
  have h3 := (allR_iff _ _ _).1 ch840001enM3 k
  by_cases a : k < 540
  · exact h0 (Nat.zero_le _) a
  by_cases b : k < 1080
  · exact h1 (by omega) b
  by_cases c : k < 1620
  · exact h2 (by omega) c
  exact h3 (by omega) (by omega)

theorem enumL_all : ∀ k < 1080, enumAt 52077576321 61871938592 1080 EL PL SL CL k = true :=
  fun k hk => (allR_iff _ _ _).1 ch840001enL k (Nat.zero_le _) hk

theorem hexaM_enum :
    Nat.card hexaM = 2160 ∧ (∀ g ∈ hexaM, g ∈ addSub ∧ ∃ k < 2160, codeL g = EM k) ∧
      ∀ k < 2160, ∃ g ∈ hexaM, codeL g = EM k := by
  obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hexaMGens = [a0, a1] := ⟨_, _, rfl⟩
  have hz : zipArrK [4439643498, 34633937090] [a0, a1] = true := by
    rw [← h]
    exact ch840004mg_code
  have hM : hexaM = grpN 64 [a0, a1] := by
    rw [← h]
  rw [hM]
  exact enum_sound hz ch840001pk.1 ch840001pk.2.1 (by norm_num) enumM_all

theorem hexaL_enum :
    Nat.card hexaL = 1080 ∧ (∀ g ∈ hexaL, g ∈ addSub ∧ ∃ k < 1080, codeL g = EL k) ∧
      ∀ k < 1080, ∃ g ∈ hexaL, codeL g = EL k := by
  obtain ⟨a0, a1, h⟩ : ∃ a0 a1, hallLGens = [a0, a1] := ⟨_, _, rfl⟩
  have hz : zipArrK [52077576321, 61871938592] [a0, a1] = true := by
    rw [← h]
    exact ch840001enLG
  have hL : hexaL = grpN 64 [a0, a1] := by
    rw [← h]
  rw [hL]
  exact enum_sound hz ch840001pk.2.2.1 ch840001pk.2.2.2 (by norm_num) enumL_all

end CFSG.KD.Hall82E
