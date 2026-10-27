
module

public import Certificates.Kernel.E64Aut.Checks
public import Certificates.Kernel.WrTwin.E64Props
public import CFSG.Certificates.Kernel.E64AutKSound
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf63E64AutBase

public section

namespace CFSG.KD.E64Aut

open CFSG.KC.WrTwin CFSG.KC.E64AutK CFSG.KD.WrTwin CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr CFSG.ClassicalInvolution.Q3.E64Data Certificates.AE117
  Certificates.E64Aut CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc.E64Aut

theorem mem_P168 {τ : Equiv.Perm (Fin 7)} (hτ : τ ∈ l32Fin ()) : lvl τ ∈ P168 := by
  have hP : P168 = (chainProds chain64).map lvl := prods_eq (e := e14) rfl chain64
  rw [hP]
  apply List.mem_map_of_mem
  have hnd := chainOK_nodup _ _ e64_chain
  have hH : ∀ σ ∈ chainProds chain64, σ ∈ l32 ⊓ alternatingGroup (Fin 7) := by
    refine chainProds_mem _ _ fun E hE e he => ?_
    have h' := of_decide_eq_true (chainOK_mem _ _ e64_chain E hE e he)
    rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup]
    exact ⟨h'.1, h'.2⟩
  have hsub : (chainProds chain64).toFinset ⊆ l32Fin () := by
    intro σ hσ
    have hg := hH σ (List.mem_toFinset.1 hσ)
    rw [Subgroup.mem_inf, Equiv.Perm.mem_alternatingGroup] at hg
    have h1 : ∀ s ∈ fanoLines, s.map σ.toEmbedding ∈ fanoLines ∧
        s.map σ⁻¹.toEmbedding ∈ fanoLines := hg.1
    simp only [l32Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h1, hg.2⟩
  have h168 : (chainProds chain64).toFinset.card = 168 := by
    rw [List.toFinset_card_of_nodup hnd, chainProds_length, e64_chain_len]
  have heq := Finset.eq_of_subset_of_card_le hsub (card_l32Fin.trans h168.symm).le
  rw [← heq] at hτ
  exact List.mem_toFinset.1 hτ

theorem facts :
    (∀ s ∈ S0 (), inM s = true) ∧ (∀ c ∈ C8 (), inM c = true) ∧ inM (ofPerm rho) = true ∧
      ofPerm rho ^ 7 = 1 ∧ (∀ s ∈ W0 (), s ∈ twinQ (2, 4, 5, 6)) ∧
      (∀ r ∈ rels, inPiP e14 pi14 (pw e14 (tab (S0 ())) r) = true) ∧
      (∀ c ∈ C8 (), c * c = 1 ∧ ∀ s ∈ W0 (), c * s = s * c) ∧ (∀ r ∈ relsK, r ∈ rels) := by
  have h := e64a_facts
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem memAtL_α₀ (b : Bool) :
    memAtL ({0, 1, 3} : Finset (Fin 7))ᶜ b = memQ (2, 4, 5, 6) b := memAtL_c0 b

theorem flag0 : FlagData ({0, 1, 3} : Finset (Fin 7))ᶜ (W0 ()) (g0 ()) (C8 ()) := by
  obtain ⟨hS, hC, -, -, hW, hrel, hcomm, hK⟩ := facts
  have hCG : CG0 = ((C8 ()).map fun c => c * g0 () * c⁻¹).map enc := by
    rw [List.map_map]
    rfl
  refine ⟨fun x hx => hS x (List.mem_append_left _ hx),
    hS (g0 ()) (List.mem_append_right _ (List.mem_singleton_self _)), hC, ?_, ?_, hcomm, ?_, ?_⟩
  · intro s hs
    have := hW s hs
    rw [twinQ, List.mem_append] at this
    rw [memAtL_α₀, memAtL_α₀]
    exact this
  · intro r hr
    have := hrel r hr
    rw [pw_eq (e := e14) rfl, inPiP_iff (e := e14) (pp := pi14) rfl rfl] at this
    exact this
  · intro a hap hav hr
    have hsol := e64a_sol
    rw [hCG] at hsol
    obtain ⟨y, hy, hay⟩ := solOK_sound (e := e14) (pp := pi14) rfl rfl hsol a (mem_P168 hap)
      (mem_V64 hav)
      (fun r hr' => hr r (hK r hr'))
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
    exact ⟨c, hc, hay⟩
  · intro y hy
    rw [allMembers_eq] at hy
    exact memOK_sound (e := e14) (pp := pi14) rfl rfl e64a_mem y hy

@[expose] def twinSet (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Set (AEQ 7) :=
  {x | ∃ a ∈ twinQ q, mkQ 7 a = x}

@[expose] def allSet : Set (AEQ 7) := {x | ∃ a ∈ membersQ, mkQ 7 a = x}

@[expose] def AutQ (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) : Prop :=
  ∀ θ : MulAut ↥e64Sub, (∀ x : ↥e64Sub, (x : AEQ 7) ∈ twinSet q → θ x = x) →
    ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub, (y : AEQ 7) ∈ allSet → θ y = c * y * c⁻¹

theorem transport {q q' : Fin 7 × Fin 7 × Fin 7 × Fin 7} (s : ↥e64Sub)
    (hf : ∀ x ∈ twinSet q, (s : AEQ 7) * x * (s : AEQ 7)⁻¹ ∈ twinSet q')
    (hb : ∀ y ∈ allSet, (s : AEQ 7)⁻¹ * y * (s : AEQ 7) ∈ allSet) (H : AutQ q) : AutQ q' := by
  intro θ hθ
  let θ' : MulAut ↥e64Sub := (MulAut.conj s).trans (θ.trans (MulAut.conj s⁻¹))
  have hθ' : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ twinSet q → θ' x = x := by
    intro x hx
    have h1 : θ (s * x * s⁻¹) = s * x * s⁻¹ := hθ _ (hf _ hx)
    simp only [θ', MulEquiv.trans_apply, MulAut.conj_apply, h1]
    group
  obtain ⟨c', hc'2, hc'⟩ := H θ' hθ'
  refine ⟨s * c' * s⁻¹, ?_, fun y hy => ?_⟩
  · calc s * c' * s⁻¹ * (s * c' * s⁻¹) = s * (c' * c') * s⁻¹ := by group
      _ = 1 := by rw [hc'2]; group
  · have h2 := hc' (s⁻¹ * y * s) (hb _ hy)
    simp only [θ', MulEquiv.trans_apply, MulAut.conj_apply] at h2
    have h3 : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rw [h3] at h2
    have h4 : θ y = s * (c' * (s⁻¹ * y * s) * c'⁻¹) * s⁻¹ := by
      rw [← h2]
      group
    rw [h4]
    group

@[expose] noncomputable def sRho : ↥e64Sub := ⟨mkQ 7 (ofPerm rho), mkQ_mem_e64Sub facts.2.2.1⟩

theorem step_sound {p : (Fin 7 × Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7 × Fin 7)}
    (hp : p ∈ quadSteps) :
    ∀ x ∈ twinSet p.1, (sRho : AEQ 7) * x * (sRho : AEQ 7)⁻¹ ∈ twinSet p.2 := by
  rintro _ ⟨a, ha, rfl⟩
  have h := List.all_eq_true.1 e64a_step p hp
  obtain ⟨y, hy, hay⟩ :=
    conjIn_sound (pp := pi14) rfl (s := ofPerm rho) (A := twinQ p.1) (B := twinQ p.2) h a ha
  refine ⟨y, hy, ?_⟩
  have h1 := (TL4.Mdl117.eqPi_iff _ _).1 hay
  rw [map_mul, map_mul, map_inv] at h1
  exact h1.symm

theorem quadSteps_cover : ∀ q ∈ quads, ∃ p ∈ quadSteps, p.1 = q ∧ p.2 ∈ quads := by
  decide +kernel

theorem allSet_conj : ∀ y ∈ allSet, (sRho : AEQ 7) * y * (sRho : AEQ 7)⁻¹ ∈ allSet := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨q, hq, haq⟩ := List.mem_flatMap.1 ha
  obtain ⟨p, hp, rfl, hp2⟩ := quadSteps_cover q hq
  obtain ⟨b, hb, hb'⟩ := step_sound hp _ ⟨a, haq, rfl⟩
  exact ⟨b, List.mem_flatMap.2 ⟨p.2, hp2, hb⟩, hb'⟩

theorem allSet_pow : ∀ n : ℕ, ∀ y ∈ allSet,
    (sRho : AEQ 7) ^ n * y * ((sRho : AEQ 7) ^ n)⁻¹ ∈ allSet
  | 0, y, hy => by simpa using hy
  | n + 1, y, hy => by
    have h := allSet_conj _ (allSet_pow n y hy)
    have e : (sRho : AEQ 7) ^ (n + 1) * y * ((sRho : AEQ 7) ^ (n + 1))⁻¹ =
        (sRho : AEQ 7) * ((sRho : AEQ 7) ^ n * y * ((sRho : AEQ 7) ^ n)⁻¹) *
          (sRho : AEQ 7)⁻¹ := by
      rw [pow_succ']
      group
    rw [e]
    exact h

theorem allSet_conj_inv : ∀ y ∈ allSet, (sRho : AEQ 7)⁻¹ * y * (sRho : AEQ 7) ∈ allSet := by
  intro y hy
  have h7 : (sRho : AEQ 7) ^ 7 = 1 := by
    change mkQ 7 (ofPerm rho) ^ 7 = 1
    rw [← map_pow, facts.2.2.2.1, map_one]
  have h6 : (sRho : AEQ 7) ^ 6 = (sRho : AEQ 7)⁻¹ := by
    rw [pow_succ] at h7
    exact eq_inv_of_mul_eq_one_left h7
  have h := allSet_pow 6 y hy
  rwa [h6, inv_inv] at h

theorem twinSet_of {α : Finset (Fin 7)} {q : Fin 7 × Fin 7 × Fin 7 × Fin 7}
    (hq : ∀ b, memAtL α b = memQ q b) (h : α.card = 4) {x : AEQ 7}
    (hx : x ∈ twinSet q) : ∃ b, x ∈ memBar α h b := by
  obtain ⟨a, ha, rfl⟩ := hx
  rw [twinQ, List.mem_append] at ha
  rcases ha with ha | ha
  · exact ⟨true, (TL4.Mdl117.mem_memBar_iff α h true _).2 ⟨a, by rw [hq]; exact ha, rfl⟩⟩
  · exact ⟨false, (TL4.Mdl117.mem_memBar_iff α h false _).2 ⟨a, by rw [hq]; exact ha, rfl⟩⟩

theorem card_compl_lines : ∀ ℓ ∈ fanoLines, (ℓᶜ).card = 4 := by decide +kernel

theorem allSet_iff (y : AEQ 7) :
    y ∈ allSet ↔ ∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), y ∈ memBar α' h' b := by
  rw [allSet, Set.mem_setOf_eq, ← allMembers_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ℓ, hℓ, ha⟩ := List.mem_flatMap.1 ha
    refine ⟨ℓᶜ, ⟨ℓ, hℓ, rfl⟩, card_compl_lines ℓ hℓ, ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · exact ⟨true, (TL4.Mdl117.mem_memBar_iff _ _ true _).2 ⟨a, ha, rfl⟩⟩
    · exact ⟨false, (TL4.Mdl117.mem_memBar_iff _ _ false _).2 ⟨a, ha, rfl⟩⟩
  · rintro ⟨α', ⟨ℓ, hℓ, rfl⟩, h', b, hy⟩
    obtain ⟨a, ha, rfl⟩ := (TL4.Mdl117.mem_memBar_iff _ h' b _).1 hy
    refine ⟨a, List.mem_flatMap.2 ⟨ℓ, hℓ, ?_⟩, rfl⟩
    cases b
    · exact List.mem_append_right _ ha
    · exact List.mem_append_left _ ha

theorem autQ0 : AutQ (2, 4, 5, 6) := by
  intro θ hθ
  have hα : (({0, 1, 3} : Finset (Fin 7))ᶜ).card = 4 := by decide +kernel
  have hfix : ∀ b, ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar ({0, 1, 3} : Finset (Fin 7))ᶜ hα b →
      θ x = x := by
    intro b x hx
    obtain ⟨a, ha, hax⟩ := (TL4.Mdl117.mem_memBar_iff _ hα b _).1 hx
    refine hθ x ⟨a, ?_, hax⟩
    rw [twinQ, List.mem_append]
    rw [memAtL_α₀] at ha
    cases b
    · exact Or.inr ha
    · exact Or.inl ha
  obtain ⟨c, hc, h⟩ := aut_core hα flag0 θ (hfix true) (hfix false)
  exact ⟨c, hc, fun y hy => h y ((allSet_iff _).1 hy)⟩

theorem autQ_step {p : (Fin 7 × Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7 × Fin 7)}
    (hp : p ∈ quadSteps) (H : AutQ p.1) : AutQ p.2 :=
  transport sRho (step_sound hp) allSet_conj_inv H

theorem autQ1 : AutQ (0, 3, 5, 6) := autQ_step (p := ((2, 4, 5, 6), (0, 3, 5, 6))) (by decide +kernel) autQ0
theorem autQ2 : AutQ (0, 1, 4, 6) := autQ_step (p := ((0, 3, 5, 6), (0, 1, 4, 6))) (by decide +kernel) autQ1
theorem autQ3 : AutQ (0, 1, 2, 5) := autQ_step (p := ((0, 1, 4, 6), (0, 1, 2, 5))) (by decide +kernel) autQ2
theorem autQ4 : AutQ (1, 2, 3, 6) := autQ_step (p := ((0, 1, 2, 5), (1, 2, 3, 6))) (by decide +kernel) autQ3
theorem autQ5 : AutQ (0, 2, 3, 4) := autQ_step (p := ((1, 2, 3, 6), (0, 2, 3, 4))) (by decide +kernel) autQ4
theorem autQ6 : AutQ (1, 3, 4, 5) := autQ_step (p := ((0, 2, 3, 4), (1, 3, 4, 5))) (by decide +kernel) autQ5

theorem aut_at {ℓ : Finset (Fin 7)} {q : Fin 7 × Fin 7 × Fin 7 × Fin 7}
    (hq : ∀ b, memAtL ℓᶜ b = memQ q b) (H : AutQ q) (θ : MulAut ↥e64Sub) (h : (ℓᶜ).card = 4)
    (hT : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar ℓᶜ h true → θ x = x)
    (hF : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar ℓᶜ h false → θ x = x) :
    ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
      (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
        θ y = c * y * c⁻¹ := by
  obtain ⟨c, hc, hy⟩ := H θ fun x hx => by
    obtain ⟨b, hb⟩ := twinSet_of hq h hx
    cases b
    · exact hF x hb
    · exact hT x hb
  exact ⟨c, hc, fun y hy' => hy y ((allSet_iff _).2 hy')⟩

theorem e64Center_k : Subgroup.center ↥e64Sub = ⊥ := by
  obtain ⟨hS, -⟩ := facts
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨a, haM, ha⟩ : ∃ a ∈ aeSubOver l32, mkQ 7 a = (z : AEQ 7) := Subgroup.mem_map.1 z.2
  obtain ⟨hav, hap⟩ := vec_perm_mem haM
  have h1 : eqPi a 1 = true := by
    refine centOK_sound (e := e14) (pp := pi14) rfl rfl e64a_cent a (mem_P168 hap) (mem_V64 hav)
      fun s hs => ?_
    rw [TL4.Mdl117.eqPi_iff]
    have hzs := Subgroup.mem_center_iff.1 hz ⟨mkQ 7 s, mkQ_mem_e64Sub (hS s hs)⟩
    have := congrArg Subtype.val hzs
    rw [map_mul, map_mul, ha]
    exact this.symm
  have h2 := (TL4.Mdl117.eqPi_iff a 1).1 h1
  rw [map_one] at h2
  apply Subtype.ext
  rw [← ha]
  exact h2

theorem e64Aut_k (θ : MulAut ↥e64Sub) {α : Finset (Fin 7)} (hα : α ∈ e64Sets) (h : α.card = 4)
    (hT : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h true → θ x = x)
    (hF : ∀ x : ↥e64Sub, (x : AEQ 7) ∈ memBar α h false → θ x = x) :
    ∃ c : ↥e64Sub, c * c = 1 ∧ ∀ y : ↥e64Sub,
      (∃ α' ∈ e64Sets, ∃ (h' : α'.card = 4) (b : Bool), (y : AEQ 7) ∈ memBar α' h' b) →
        θ y = c * y * c⁻¹ := by
  obtain ⟨ℓ, hℓ, rfl⟩ := hα
  simp only [fanoLines, List.mem_cons, List.not_mem_nil, or_false] at hℓ
  rcases hℓ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact aut_at memAtL_c0 autQ0 θ h hT hF
  · exact aut_at memAtL_c1 autQ1 θ h hT hF
  · exact aut_at memAtL_c2 autQ2 θ h hT hF
  · exact aut_at memAtL_c3 autQ3 θ h hT hF
  · exact aut_at memAtL_c4 autQ4 θ h hT hF
  · exact aut_at memAtL_c5 autQ5 θ h hT hF
  · exact aut_at memAtL_c6 autQ6 θ h hT hF

end CFSG.KD.E64Aut

end
