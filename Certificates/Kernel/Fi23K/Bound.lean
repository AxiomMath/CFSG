module

public import Certificates.Kernel.Fi23K.Card
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Fi23
public import Certificates.Kernel.Fi23K.Chain
public import Certificates.Kernel.Sporadic.Fi23Br.Words

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Fi23K CFSG.KS.PC CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native TauCeti

@[expose] def wordVal {H : Type*} [Group H] (x : ℕ → H) (w : List (ℕ × Bool)) : H :=
  (w.map fun l => if l.2 then x l.1 else (x l.1)⁻¹).prod

theorem lift_rel (P : GroupPresentation) {H : Type*} [Group H] (x : ℕ → H)
    (hrel : ∀ w ∈ P.relatorLetters, wordVal x w = 1) :
    ∀ r ∈ P.relatorSet, FreeGroup.lift (fun i : Fin P.generatorCount => x i.val) r = 1 := by
  intro r hr
  rw [CFSG.Sporadic.Presentation.relatorSet_eq] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [FreeGroup.lift_mk]
  have := hrel (w.map fun l => (l.1.val, l.2))
    (by rw [TauCeti.GroupPresentation.relatorLetters_def]; exact List.mem_map_of_mem hw)
  unfold wordVal at this
  rw [List.map_map] at this
  rw [← this]
  congr 1
  apply List.map_congr_left
  rintro ⟨g, b⟩ _
  cases b <;> rfl

@[expose] noncomputable def presHom (P : GroupPresentation) {H : Type*} [Group H] (x : ℕ → H)
    (hrel : ∀ w ∈ P.relatorLetters, wordVal x w = 1) : PresentedGroup P.relatorSet →* H :=
  PresentedGroup.toGroup (lift_rel P x hrel)

theorem presHom_of (P : GroupPresentation) {H : Type*} [Group H] (x : ℕ → H)
    (hrel : ∀ w ∈ P.relatorLetters, wordVal x w = 1) (i : Fin P.generatorCount) :
    presHom P x hrel (PresentedGroup.of i) = x i :=
  PresentedGroup.toGroup.of (lift_rel P x hrel)

theorem closure_le_range (P : GroupPresentation) {H : Type*} [Group H] (x : ℕ → H)
    (hrel : ∀ w ∈ P.relatorLetters, wordVal x w = 1) :
    Subgroup.closure (x '' {g | g < P.generatorCount}) ≤ (presHom P x hrel).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨PresentedGroup.of ⟨g, hg⟩, presHom_of P x hrel ⟨g, hg⟩⟩

noncomputable abbrev P23 : GroupPresentation := SporadicName.Fi23.presentation

private theorem P23_eq : P23 = Sporadic.fi23Presentation := rfl

theorem relatorLetters_P23 : P23.relatorLetters = CFSG.Sporadic.Bridge.Fi23GPL.Native.rels () := by
  rw [P23_eq, Sporadic.fi23Presentation_relatorLetters]
  rfl

theorem generatorCount_P23 : P23.generatorCount = 10 := by
  rw [P23_eq]
  simp [GroupPresentation.generatorCount]

theorem rels_X : ∀ w ∈ P23.relatorLetters, wordVal xS w = 1 := by
  rw [relatorLetters_P23]
  exact rels_one

@[expose] noncomputable def phiX : PresentedGroup P23.relatorSet →* Equiv.Perm (Fin 31671) :=
  presHom P23 xS rels_X

theorem range_phiX : phiX.range = Xc := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨i.val, lt_of_lt_of_eq i.isLt generatorCount_P23,
      (presHom_of P23 xS rels_X i).symm⟩
  · have h := closure_le_range P23 xS rels_X
    have hs : {g | g < P23.generatorCount} = {g | g < 10} := by
      ext g
      simp [generatorCount_P23]
    rw [hs] at h
    exact h

theorem card_Xc : Nat.card Xc ≤ 4089470473293004800 := by
  obtain ⟨hf, hc⟩ := CFSG.Sporadic.Presentation.Fi23.finite_card_le
  have hf' : Finite (PresentedGroup P23.relatorSet) := hf
  rw [← range_phiX]
  exact (Nat.card_le_card_of_surjective _ phiX.rangeRestrict_surjective).trans hc

theorem word_mem : ∀ w : List Nat, (∀ r ∈ w, ∃ p ∈ Xc, ActsAs p (tb G r)) →
    ∃ p ∈ Xc, ActsAs p (wv G w)
  | [], _ => ⟨1, Subgroup.one_mem _, fun _ _ => rfl⟩
  | r :: w, hw => by
    obtain ⟨q, hq, hqa⟩ := word_mem w fun s hs => hw s (List.mem_cons_of_mem r hs)
    obtain ⟨p, hp, hpa⟩ := hw r List.mem_cons_self
    exact ⟨p * q, Subgroup.mul_mem _ hp hq, hpa.mul hqa⟩

theorem surj_data :
    exW rhsF 20 (ER 94) = (CFSG.KD.BrFi23.ST.W.getD 0 []).map (fun z => z.natAbs - 1) ∧
    exW rhsF 20 (ER 95) = (CFSG.KD.BrFi23.ST.W.getD 1 []).map (fun z => z.natAbs - 1) ∧
    (∀ s ∈ ER 94, s < 91) ∧ (∀ s ∈ ER 95, s < 91) ∧ EL 94 = [39] ∧ EL 95 = [40] ∧
    (∀ s ∈ (CFSG.KD.BrFi23.ST.W.getD 0 []).map (fun z => z.natAbs - 1), s < 10) ∧
    (∀ s ∈ (CFSG.KD.BrFi23.ST.W.getD 1 []).map (fun z => z.natAbs - 1), s < 10) := by
  decide +kernel

@[expose] noncomputable def sw (i : Nat) : List Nat :=
  (CFSG.KD.BrFi23.ST.W.getD i []).map (fun z => z.natAbs - 1)

theorem reg_word {k r : Nat} (hk : k < 150) (hl : EL k = [r]) (hs : ∀ s ∈ ER k, s < 91) {w : List Nat}
    (hw : exW rhsF 20 (ER k) = w) : ∀ x < 31671, tb G r x = wv G w x := by
  intro x hx
  have h := eqv hk hx
  rw [hl] at h
  rw [← hw, ← expand 20 hs hx]
  exact h

theorem alpha_acts : ActsAs ((sw 0).map xS).prod (tb G 39) := by
  obtain ⟨h0, -, hs0, -, hl0, -, hx0, -⟩ := surj_data
  intro x hx
  rw [(word_acts (sw 0) hx0).1 x hx, reg_word (by norm_num) hl0 hs0 h0 x hx]
  rfl

theorem beta_acts : ActsAs ((sw 1).map xS).prod (tb G 40) := by
  obtain ⟨-, h1, -, hs1, -, hl1, -, hx1⟩ := surj_data
  intro x hx
  rw [(word_acts (sw 1) hx1).1 x hx, reg_word (by norm_num) hl1 hs1 h1 x hx]
  rfl

theorem sw_mem (i : Nat) (hi : i < 2) : ((sw i).map xS).prod ∈ Xc := by
  obtain ⟨-, -, -, -, -, -, hx0, hx1⟩ := surj_data
  interval_cases i
  · exact (word_acts _ hx0).2
  · exact (word_acts _ hx1).2

theorem atom_mem {r : Nat} (hr : r = 39 ∨ r = 40 ∨ r = 41) : ∃ p ∈ Xc, ActsAs p (tb G r) := by
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, sw_mem 0 (by norm_num), alpha_acts⟩
  · exact ⟨_, sw_mem 1 (by norm_num), beta_acts⟩
  · exact ⟨_, Subgroup.inv_mem _ (sw_mem 1 (by norm_num)),
      beta_acts.inv (rng 41 (by norm_num)) fun _ hx => binv_right hx⟩

theorem letters_mem_aux : ∀ j ≤ 12, ∀ l < 2 * j, ∃ p ∈ Xc, ActsAs p (LL l)
  | 0, _ => fun l hl => absurd hl (by omega)
  | j + 1, hj => by
    have ih := letters_mem_aux j (by omega)
    obtain ⟨-, hw⟩ := words_data
    obtain ⟨hz, hzr, hex, hER, hEL, -, -⟩ := hw j (by omega)
    have heven : ∃ p ∈ Xc, ActsAs p (LL (2 * j)) := by
      have hreg : ∀ x < 31671, LL (2 * j) x = wv G (((chainWords ())[j]!).map regZ) x := by
        intro x hx
        unfold LL
        exact reg_word (by omega) hEL hER hex x hx
      obtain ⟨p, hp, hpa⟩ := word_mem (((chainWords ())[j]!).map regZ) (by
        intro r hr
        obtain ⟨z, hzm, rfl⟩ := List.mem_map.1 hr
        obtain ⟨hz0, hzj⟩ := hz z hzm
        unfold regZ
        by_cases h1 : z = 1 ∨ z = -1
        · rw [if_pos h1]
          exact atom_mem (Or.inl rfl)
        rw [if_neg h1]
        by_cases h2 : z = 2
        · rw [if_pos h2]
          exact atom_mem (Or.inr (Or.inl rfl))
        rw [if_neg h2]
        by_cases h3 : z = -2
        · rw [if_pos h3]
          exact atom_mem (Or.inr (Or.inr rfl))
        rw [if_neg h3]
        have hj' : z.natAbs - 3 < j := by omega
        by_cases hp : 0 < z
        · rw [if_pos hp]
          obtain ⟨p, hp, hpa⟩ := ih (2 * (z.natAbs - 3)) (by omega)
          exact ⟨p, hp, hpa⟩
        · rw [if_neg hp]
          obtain ⟨p, hp, hpa⟩ := ih (2 * (z.natAbs - 3) + 1) (by omega)
          refine ⟨p, hp, fun x hx => ?_⟩
          rw [hpa x hx]
          unfold LL
          congr 1
          change 52 + (2 * (z.natAbs - 3) + 1) = _
          omega)
      exact ⟨p, hp, fun x hx => by rw [hpa x hx, hreg x hx]⟩
    intro l hl
    rcases (by omega : l < 2 * j ∨ l = 2 * j ∨ l = 2 * j + 1) with h | rfl | rfl
    · exact ih l h
    · exact heven
    · obtain ⟨p, hp, hpa⟩ := heven
      refine ⟨p⁻¹, Subgroup.inv_mem _ hp, hpa.inv (fun x hx => LL_lt (by omega) hx) ?_⟩
      exact right_inv_of_left (fun x hx => LL_lt (by omega) hx) (fun x hx => LL_lt (by omega) hx)
        (fun x hx => letter_inv (by omega) hx)

theorem letter_mem {l : Nat} (hl : l < 24) : permOfT 31671 (chainLetters orbLit)[l]! ∈ Xc := by
  obtain ⟨p, hp, hpa⟩ := letters_mem_aux 12 le_rfl l hl
  have e : permOfT 31671 (chainLetters orbLit)[l]! = p := by
    ext ⟨x, hx⟩
    have := sig_val chain_hyp hl ⟨x, hx⟩
    unfold sig at this
    rw [this, hpa x hx]
  rw [e]
  exact hp

theorem hcard : Hcard := by
  have hle : Subgroup.closure (Set.range fun l : Fin 24 =>
      permOfT 31671 (chainLetters orbLit)[l.val]!) ≤ Xc := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact letter_mem l.isLt
  have : Finite (Equiv.Perm (Fin 31671)) := inferInstance
  exact (Subgroup.card_le_of_le hle).trans card_Xc

end CFSG.KD.Fi23K

end
