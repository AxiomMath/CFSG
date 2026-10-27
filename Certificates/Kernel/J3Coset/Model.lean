module

public import Certificates.Kernel.J3Coset.Outer
public import CFSG.Sporadic.Bridge.J3Surj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Sporadic.Bridge.Common

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.J3C CFSG.KD.J3C CFSG.KS MulAction CFSG.AGLEmbedding.KFactProofs.J3Sylow
  CFSG.AGLEmbedding.KFactProofs.J3Cover CFSG.Quasithin CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen TauCeti

@[expose] def codeL (l : ℕ × Bool) : ℕ :=
  if l.1 = 0 then (if l.2 then 0 else 1) else (if l.2 then 2 else 3)

private theorem presentation_eq : SporadicName.J3.presentation = Sporadic.j3Presentation := rfl

theorem rel_eq : Sporadic.j3Presentation.relatorLetters.map (List.map codeL) = rels := by
  simp [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def,
    Sporadic.j3Presentation_transcribed, FreeGroup.invRev]
  decide +kernel

@[expose] noncomputable def permA : Equiv.Perm (Fin nn) where
  toFun i := ⟨tb 0 i.val, (perm_facts _ i.isLt).1⟩
  invFun i := ⟨tb 0 i.val, (perm_facts _ i.isLt).1⟩
  left_inv i := Fin.ext (perm_facts _ i.isLt).2.1
  right_inv i := Fin.ext (perm_facts _ i.isLt).2.1

@[expose] noncomputable def permB : Equiv.Perm (Fin nn) where
  toFun i := ⟨tb 2 i.val, (perm_facts _ i.isLt).2.2.1⟩
  invFun i := ⟨tb 3 i.val, (perm_facts _ i.isLt).2.2.2.1⟩
  left_inv i := Fin.ext (perm_facts _ i.isLt).2.2.2.2.1
  right_inv i := Fin.ext (perm_facts _ i.isLt).2.2.2.2.2.1

@[expose] noncomputable def genP (c : ℕ) : Equiv.Perm (Fin nn) :=
  if c = 0 then permA else if c = 1 then permA⁻¹ else if c = 2 then permB else permB⁻¹

theorem genP_act (c : ℕ) (hc : c < 4) (i : Fin nn) : (genP c i).val = tb c i.val := by
  unfold genP
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem wordProd_eq_ev (v : List (ℕ × Bool)) :
    CFSG.Sporadic.Bridge.wordProd (img2 permA permB) v = ev genP (v.map codeL) := by
  induction v with
  | nil => rfl
  | cons l v ih =>
    have e1 : CFSG.Sporadic.Bridge.wordProd (img2 permA permB) (l :: v) =
        (if l.2 then img2 permA permB l.1 else (img2 permA permB l.1)⁻¹) *
          CFSG.Sporadic.Bridge.wordProd (img2 permA permB) v := by
      simp [CFSG.Sporadic.Bridge.wordProd]
    rw [e1, ih, List.map_cons, ev_cons]
    congr 1
    obtain ⟨i, s⟩ := l
    unfold codeL genP img2
    by_cases hi : i = 0 <;> cases s <;> simp [hi]

theorem relators : ∀ v ∈ (SporadicName.J3.presentation).relatorLetters,
    CFSG.Sporadic.Bridge.wordProd (img2 permA permB) v = 1 := by
  intro v hv
  rw [presentation_eq] at hv
  have hmem : v.map codeL ∈ rels := by
    rw [← rel_eq]
    exact List.mem_map_of_mem hv
  have hcodes : ∀ c ∈ v.map codeL, c < 4 := by
    intro c hc
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hc
    unfold codeL
    split_ifs <;> omega
  rw [wordProd_eq_ev]
  ext i
  have h := act_ev (MonoidHom.id _) genP tb _ (fun c hc j => genP_act c (hcodes c hc) j) i
  simp only [MonoidHom.id_apply] at h
  rw [h, Equiv.Perm.one_apply]
  exact rel_facts i.val i.isLt _ hmem

@[expose] noncomputable def psi : (TauCeti.CFSGIndex.sporadic .J3).Group →* Equiv.Perm (Fin nn) :=
  presHom SporadicName.J3.presentation (img2 permA permB) relators

theorem psi_gen0 : psi (presGen SporadicName.J3.presentation 0) = permA := by
  unfold psi
  rw [presHom_presGen _ _ relators (by rw [presentation_eq, CFSG.Sporadic.Bridge.J3.generatorCount_eq]; omega)]
  rfl

theorem psi_gen1 : psi (presGen SporadicName.J3.presentation 1) = permB := by
  unfold psi
  rw [presHom_presGen _ _ relators (by rw [presentation_eq, CFSG.Sporadic.Bridge.J3.generatorCount_eq]; omega)]
  rfl

section Iso

variable {J : Type} [Group J]

@[expose] noncomputable def actE (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :
    J →* Equiv.Perm (Fin nn) := psi.comp e.toMonoidHom

@[expose] noncomputable def instE (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :
    MulAction J (Fin nn) := MulAction.compHom (Fin nn) (actE e)

@[expose] noncomputable def g0E (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : ℕ) : J :=
  if c = 0 then e.symm (presGen SporadicName.J3.presentation 0)
  else if c = 1 then (e.symm (presGen SporadicName.J3.presentation 0))⁻¹
  else if c = 2 then e.symm (presGen SporadicName.J3.presentation 1)
  else (e.symm (presGen SporadicName.J3.presentation 1))⁻¹

@[expose] noncomputable def g1E (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : ℕ) : J :=
  if c < 4 then g0E e c else if c = 4 then ev (g0E e) wK1 else ev (g0E e) wK2

@[expose] noncomputable def gE (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : ℕ) : J :=
  if c < 6 then g1E e c else if c = 6 then ev (g1E e) wP1 else ev (g1E e) wP2

theorem act0 (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : ℕ) (hc : c < 4)
    (i : Fin nn) : (actE e (g0E e c) i).val = tb c i.val := by
  have ha : actE e (e.symm (presGen SporadicName.J3.presentation 0)) = permA := by
    simp only [actE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact psi_gen0
  have hb : actE e (e.symm (presGen SporadicName.J3.presentation 1)) = permB := by
    simp only [actE, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact psi_gen1
  rw [← genP_act c hc i]
  have key : actE e (g0E e c) = genP c := by
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
    · simp only [g0E, genP, ↓reduceIte]
      exact ha
    · simp only [g0E, genP, show (1 : ℕ) ≠ 0 from by decide, if_false, if_true, map_inv]
      rw [ha]
    · simp only [g0E, genP, show (2 : ℕ) ≠ 0 from by decide, show (2 : ℕ) ≠ 1 from by decide,
        if_false, if_true]
      exact hb
    · simp only [g0E, genP, show (3 : ℕ) ≠ 0 from by decide, show (3 : ℕ) ≠ 1 from by decide,
        show (3 : ℕ) ≠ 2 from by decide, if_false, map_inv]
      rw [hb]
  rw [key]

theorem act1 (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : ℕ) (hc : c < 6)
    (i : Fin nn) : (actE e (g1E e c) i).val = tb c i.val := by
  unfold g1E
  by_cases h4 : c < 4
  · rw [if_pos h4]
    exact act0 e c h4 i
  · rw [if_neg h4]
    have hk : ∀ w, codesAB w = true → ∀ i : Fin nn,
        (actE e (ev (g0E e) w) i).val = wv tb w i.val := fun w hw =>
      act_ev (actE e) (g0E e) tb w fun d hd j => act0 e d (by
        have := codesAB_lt hw d hd
        unfold codesAB at hw
        have h2 := List.all_eq_true.1 hw d hd
        simpa using h2) j
    by_cases h5 : c = 4
    · subst h5
      rw [if_pos rfl, hk _ fix_facts.2.2.2.2.2.2.1]
      exact ((k_facts i.val i.isLt).1).symm
    · have h5' : c = 5 := by omega
      subst h5'
      rw [if_neg (by decide), hk _ fix_facts.2.2.2.2.2.2.2.1]
      exact ((k_facts i.val i.isLt).2).symm

theorem actG (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : ℕ) (hc : c < 8)
    (i : Fin nn) : (actE e (gE e c) i).val = tb c i.val := by
  unfold gE
  by_cases h6 : c < 6
  · rw [if_pos h6]
    exact act1 e c h6 i
  · rw [if_neg h6]
    have hp : ∀ w, codesIn 4 5 w = true → ∀ i : Fin nn,
        (actE e (ev (g1E e) w) i).val = wv tb w i.val := fun w hw =>
      act_ev (actE e) (g1E e) tb w fun d hd j => act1 e d (by
        rcases codesIn_mem hw d hd with rfl | rfl <;> decide) j
    by_cases h7 : c = 6
    · subst h7
      rw [if_pos rfl, hp _ fix_facts.2.2.2.2.2.2.2.2.1]
      exact ((p_facts i.val i.isLt).1).symm
    · have h7' : c = 7 := by omega
      subst h7'
      rw [if_neg (by decide), hp _ fix_facts.2.2.2.2.2.2.2.2.2.1]
      exact ((p_facts i.val i.isLt).2).symm

theorem acts (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :
    @Acts J _ (instE e) (gE e) := fun c hc i => actG e c hc i

theorem gen_top (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) :
    Subgroup.closure ({gE e 0, gE e 2} : Set J) = ⊤ := by
  set P := SporadicName.J3.presentation
  have hP : P.generatorCount = 2 := CFSG.Sporadic.Bridge.J3.generatorCount_eq
  have hX : Subgroup.closure ({presGen P 0, presGen P 1} : Set P.Group) = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of P.relatorSet, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    apply Subgroup.subset_closure
    have hgen : presGen P i.val = PresentedGroup.of i := by
      simp only [CFSG.Sporadic.Bridge.presGen, dif_pos i.2]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases (by have := i.2; omega : i.val = 0 ∨ i.val = 1) with h | h
    · left
      rw [← hgen, h]
    · right
      rw [← hgen, h]
  have h := congrArg (Subgroup.map e.symm.toMonoidHom) hX
  rw [MonoidHom.map_closure, Set.image_pair,
    Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  have h0 : gE e 0 = e.symm (presGen P 0) := by simp [gE, g1E, g0E, P]
  have h2 : gE e 2 = e.symm (presGen P 1) := by simp [gE, g1E, g0E, P]
  rw [h0, h2]
  exact h

@[expose] noncomputable def twist (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : J) :
    J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group :=
  (MulAut.conj c).symm.trans e

theorem gE_twist (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : J) (k : ℕ) :
    gE (twist e c) k = MulAut.conj c (gE e k) := by
  have hs : ∀ x, (twist e c).symm x = MulAut.conj c (e.symm x) := fun x => rfl
  have h0 : ∀ k, g0E (twist e c) k = MulAut.conj c (g0E e k) := by
    intro k
    unfold g0E
    split_ifs
    · rw [hs]
    · rw [hs, map_inv]
    · rw [hs]
    · rw [hs, map_inv]
  have h1 : ∀ k, g1E (twist e c) k = MulAut.conj c (g1E e k) := by
    intro k
    unfold g1E
    have hf : g0E (twist e c) = fun k => MulAut.conj c (g0E e k) := funext h0
    split_ifs
    · exact h0 k
    · rw [hf]; exact (map_ev (MulAut.conj c).toMonoidHom _ _).symm
    · rw [hf]; exact (map_ev (MulAut.conj c).toMonoidHom _ _).symm
  unfold gE
  have hf : g1E (twist e c) = fun k => MulAut.conj c (g1E e k) := funext h1
  split_ifs
  · exact h1 k
  · rw [hf]; exact (map_ev (MulAut.conj c).toMonoidHom _ _).symm
  · rw [hf]; exact (map_ev (MulAut.conj c).toMonoidHom _ _).symm

theorem PP_twist (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) (c : J) :
    PP (gE (twist e c)) = (PP (gE e)).map (MulAut.conj c).toMonoidHom := by
  rw [PP, PP, MonoidHom.map_closure, Set.image_pair, gE_twist, gE_twist]
  rfl

variable [Finite J]

theorem P_sylow (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)
    (hJ : Nat.card J = 50232960) :
    IsPGroup 3 (@PP J _ (gE e)) ∧ ¬ 3 ∣ (@PP J _ (gE e)).index := by
  letI := instE e
  have hc := card_P (acts e) hJ
  refine ⟨IsPGroup.of_card (n := 5) (by rw [hc]; norm_num), ?_⟩
  have := Subgroup.card_mul_index (PP (gE e))
  rw [hc, hJ] at this
  have hi : (PP (gE e)).index = 206720 := by omega
  rw [hi]
  norm_num

@[expose] noncomputable def sylP (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)
    (hJ : Nat.card J = 50232960) : Sylow 3 J :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (P_sylow e hJ).1.toSylow (P_sylow e hJ).2

theorem exists_twist (e : J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)
    (hJ : Nat.card J = 50232960) (T : Sylow 3 J) :
    ∃ c : J, PP (gE (twist e c)) = (T : Subgroup J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq J (sylP e hJ) T
  refine ⟨c, ?_⟩
  rw [PP_twist]
  have h2 : ((c • sylP e hJ : Sylow 3 J) : Subgroup J) =
      ((sylP e hJ : Sylow 3 J) : Subgroup J).map (MulAut.conj c).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hc] at h2
  exact h2.symm

end Iso

theorem fact9435 : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → ∀ T : Sylow 3 J, ∃ (H : Subgroup J) (t₁ t₂ s : J)
        (Z : Fin 9 → J) (w₁ w₂ : List Bool), Subgroup.closure ({t₁, t₂} : Set J) = T ∧
          IsCoatom H ∧ LocalData H t₁ t₂ s Z w₁ w₂ := by
  intro J _ _ ⟨e⟩ hs hJ T
  obtain ⟨c, hc⟩ := exists_twist e hJ T
  letI := instE (twist e c)
  exact ⟨stabilizer J pt0, gE (twist e c) 6, gE (twist e c) 7, gE (twist e c) 5,
    zz (gE (twist e c)), sw1, sw2, hc, coatom (acts _) hJ, localData (acts _) hJ⟩

theorem fact9465 : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → (∃ x d₁ d₂ g u : J, CoverData x d₁ d₂ g u) ∧
        ∀ T : Sylow 3 J, ∀ K : Subgroup J, (T : Subgroup J) ≤ K →
          K ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) ∨ K = ⊤ := by
  intro J _ _ ⟨e⟩ hs hJ
  refine ⟨?_, fun T K hTK => ?_⟩
  · letI := instE e
    exact ⟨_, _, _, _, _, coverData (acts e) hJ⟩
  · obtain ⟨c, hc⟩ := exists_twist e hJ T
    letI := instE (twist e c)
    rw [← hc] at hTK ⊢
    exact overgroup (acts _) hJ hTK

theorem fact9466 : ∀ (J : Type) [Group J] [Finite J],
    Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group) → IsSimpleGroup J →
      Nat.card J = 50232960 → ∃ (T : Sylow 3 J) (φ : MulAut J),
        (∀ x ∈ (T : Subgroup J), φ x ∈ (T : Subgroup J)) ∧
        φ ∉ (MulAut.conj : J →* MulAut J).range ∧
        (∀ z ∈ centerOf (T : Subgroup J), z ≠ 1 →
          Subgroup.centralizer {z} ≤ Subgroup.normalizer ((T : Subgroup J) : Set J) →
          Subgroup.centralizer {z} ≤ T) ∧
        (∀ x ∈ Subgroup.normalizer ((T : Subgroup J) : Set J), (MulAut.conj x * φ) ^ 2 = 1 →
          ∀ E : Subgroup J, E ≤ T → IsMulCommutative E → (∀ y ∈ E, y ^ 3 = 1) →
            Nat.card E = 9 → ∃ y ∈ E, (MulAut.conj x * φ) y ≠ y) := by
  intro J _ _ ⟨e⟩ hs hJ
  letI := instE e
  obtain ⟨φ, h1, h2, h3, h4⟩ := outer (acts e) hJ (gen_top e)
  exact ⟨sylP e hJ, φ, h1, h2, h3, h4⟩

end CertificateChecks.KernelJ3C

end
