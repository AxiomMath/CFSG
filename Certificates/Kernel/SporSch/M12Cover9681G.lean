module

public import Certificates.Kernel.SporSch.M12Cover9681
public import CFSG.Certificates.Kernel.Misc.SylKeySound
public import CFSG.Certificates.Kernel.L52Insp443.Scan
public import CFSG.Sporadic.Schreier.M12

public section

namespace CertificateChecks.KernelSporSch.M12Cover9681

open CFSG.KC.SylKey CFSG.AGLEmbedding.KFactProofs.M12Cover CFSG.Sporadic.Mathieu CFSG.Blueprint
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

abbrev Rs : List (Equiv.Perm (Fin 12)) := m12CoverReps.map (·.1)

theorem lens_spec : m12CoverNorm.length = 54 ∧ m12CoverReps.length = 80 ∧ E5.length = 2376 ∧
    E11.length = 1728 ∧ X5.length = 40 ∧ X11.length = 55 ∧ WN.length = 54 ∧ WR.length = 80 ∧
    R5 < 80 ∧ R11 < 80 := by
  have h := lens
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem gens_spec : cd m12gA = gA ∧ cd m12gB = gB ∧ cd m12gB⁻¹ = gBI := by
  have h := pinG
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem gA_mem : m12gA ∈ NativeSporadic.M12 := by
  rw [m12_eq]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem gB_mem : m12gB ∈ NativeSporadic.M12 := by
  rw [m12_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem gBI_mem : m12gB⁻¹ ∈ NativeSporadic.M12 := Subgroup.inv_mem _ gB_mem

theorem mem_of_word {T : Nat} {W : List (List Nat)} (hW : wB gA gB gBI T W 0 = true)
    {σ : Equiv.Perm (Fin 12)} {i : Nat} (hi : i < W.length) (hσ : lk T i = cd σ) :
    σ ∈ NativeSporadic.M12 := by
  have h1 := wB_spec hW i hi
  rw [zero_add, hσ] at h1
  obtain ⟨hA, hB, hBI⟩ := gens_spec
  obtain ⟨τ, hτ, he⟩ := wev_spec gA_mem gB_mem gBI_mem W[i]
  rw [hA, hB, hBI, h1] at he
  rw [cd_inj he]
  exact hτ

theorem norm_spec {i : Nat} (hi : i < 54) :
    ∃ hi' : i < m12CoverNorm.length, lk NT i = cd m12CoverNorm[i] ∧
      lk NIT i = cd m12CoverNorm[i]⁻¹ := by
  have hl := lens_spec.1
  have hi' : i < m12CoverNorm.length := by omega
  refine ⟨hi', ?_, ?_⟩
  · have := pinB_spec pinN i hi'
    rwa [zero_add] at this
  · have := pinB_spec pinNI i (by simpa using hi')
    rwa [zero_add, List.getElem_map] at this

theorem rep_spec {j : Nat} (hj : j < 80) :
    ∃ hj' : j < Rs.length, lk RT j = cd Rs[j] := by
  have hl := lens_spec.2.1
  have hj' : j < Rs.length := by simp [Rs]; omega
  refine ⟨hj', ?_⟩
  have := pinB_spec pinR j hj'
  rwa [zero_add] at this

theorem norm_mem {n : Equiv.Perm (Fin 12)} (hn : n ∈ m12CoverNorm) : n ∈ NativeSporadic.M12 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hn
  obtain ⟨hl1, -, -, -, -, -, hl7, -⟩ := lens_spec
  obtain ⟨hi', h1, -⟩ := norm_spec (i := i) (by omega)
  exact mem_of_word wn (by omega) h1

theorem rep_mem {r : Equiv.Perm (Fin 12)} (hr : r ∈ Rs) : r ∈ NativeSporadic.M12 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
  obtain ⟨-, hl2, -, -, -, -, -, hl8, -⟩ := lens_spec
  have hj80 : j < 80 := by simpa [Rs, hl2] using hj
  obtain ⟨hj', h1⟩ := rep_spec hj80
  exact mem_of_word wr (by omega) h1

theorem hN : ∀ i < 54, ∃ n ∈ m12CoverNorm, lk NT i = cd n ∧ lk NIT i = cd n⁻¹ := by
  intro i hi
  obtain ⟨hi', h1, h2⟩ := norm_spec hi
  exact ⟨_, List.getElem_mem hi', h1, h2⟩

theorem hR : ∀ j < 80, ∃ r ∈ Rs, lk RT j = cd r := by
  intro j hj
  obtain ⟨hj', h1⟩ := rep_spec hj
  exact ⟨_, List.getElem_mem hj', h1⟩

theorem cover_p {p : Nat} [Fact p.Prime] (hH : ¬ p ^ 2 ∣ 95040) {E : List (Nat × Nat)}
    (hE : allE p NT NIT RT E 0 = true) {R : Nat} (hR80 : R < 80)
    (ho : ordB p (lk RT R) = true) {X : List (List Nat × Nat)}
    (hX : nrmB gA gB gBI (lk RT R) X 0 = true) (hcard : 95040 ≤ E.length * X.length)
    {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    (hgo : orderOf g = p) :
    ∃ i, 1 ≤ i ∧ i ≤ p - 1 ∧ ∃ n ∈ m12CoverNorm, ∃ r ∈ Rs, g ^ i = n * r * n⁻¹ := by
  obtain ⟨cs, hl, hnd, hcs⟩ := allE_spec hN hR hE
  obtain ⟨hR', hr0⟩ := rep_spec hR80
  rw [hr0] at ho hX
  obtain ⟨hA, hB, hBI⟩ := gens_spec
  rw [← hA, ← hB, ← hBI] at hX
  obtain ⟨xs, hxl, hxd, hxs⟩ := nrmB_spec gA_mem gB_mem gBI_mem hX
  have hc : ∀ c ∈ cs, c ∈ NativeSporadic.M12 := by
    intro c hc
    obtain ⟨-, -, n, hn, r, hr, rfl⟩ := hcs c hc
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (norm_mem hn) (rep_mem hr))
      (Subgroup.inv_mem _ (norm_mem hn))
  obtain ⟨c, hcm, hz⟩ := sylow_cover NativeSporadic.M12 (by rwa [m12_card])
    (rep_mem (List.getElem_mem hR')) (ordB_spec ho) (fun x hx => (hxs x hx).1)
    (fun x hx => (hxs x hx).2.2) hxd hc (fun c hc => (hcs c hc).1) hnd
    (by rw [m12_card, hl, hxl]; exact hcard) hg hgo
  obtain ⟨hco, -, n, hn, r, hr, hcnr⟩ := hcs c hcm
  have hne : c ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hco
    exact (Fact.out : p.Prime).one_lt.ne hco
  obtain ⟨i, hi1, hi2, hi⟩ := exists_pow_of_mem hgo (hz ▸ Subgroup.mem_zpowers c) hne
  exact ⟨i, hi1, hi2, n, hn, r, hr, hi ▸ hcnr⟩

theorem exists_conj_pow {g : Equiv.Perm (Fin 12)}
    (hg : g ∈ NativeSporadic.M12) (ho : orderOf g = 5 ∨ orderOf g = 11) :
    ∃ i, 1 ≤ i ∧ i ≤ 10 ∧ ∃ n ∈ m12CoverNorm, ∃ r ∈ Rs, g ^ i = n * r * n⁻¹ := by
  have hl := lens_spec
  rcases ho with ho | ho
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨i, h1, h2, h⟩ := cover_p (by norm_num) e5 hl.2.2.2.2.2.2.2.2.1 o5 x5
      (by rw [hl.2.2.1, hl.2.2.2.2.1]) hg ho
    exact ⟨i, h1, by omega, h⟩
  · have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨i, h1, h2, h⟩ := cover_p (by norm_num) e11 hl.2.2.2.2.2.2.2.2.2 o11 x11
      (by rw [hl.2.2.2.1, hl.2.2.2.2.2.1]) hg ho
    exact ⟨i, h1, by omega, h⟩

theorem compT_ext {P Q P' Q' : Table} {g : Equiv.Perm (Fin 12)} (h : Rep 12 (compT 12 P Q) g)
    (h' : Rep 12 (compT 12 P' Q') g) : compT 12 P Q = compT 12 P' Q' := by
  apply Array.ext
  · simp [compT]
  · intro i hi hi'
    have hi12 : i < 12 := by simpa [compT] using hi
    have e1 := h i hi12
    rw [← h' i hi12] at e1
    unfold ap at e1
    rw [getElem!_pos (compT 12 P Q) i hi, getElem!_pos (compT 12 P' Q') i hi'] at e1
    exact UInt32.toNat_inj.1 e1

theorem bad_false {g : Equiv.Perm (Fin 12)}
    (hg : g ∈ NativeSporadic.M12) {T : Table} (hT : Rep 12 T g) : m12CoverBad T = false := by
  unfold m12CoverBad
  by_cases ho : orderOf g = 5 ∨ orderOf g = 11
  · obtain ⟨i, hi1, hi2, n, hn, r, hr, hgi⟩ := exists_conj_pow hg ho
    obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    have hcov : m12CoverCov T = true := by
      unfold m12CoverCov
      rw [List.any_eq_true]
      refine ⟨i - 1, List.mem_range.2 (by omega), ?_⟩
      unfold m12CoverOrbSet
      rw [Std.HashSet.contains_ofList, List.contains, List.elem_eq_mem, decide_eq_true_eq,
        m12CoverOrb]
      simp only [List.mem_flatMap, List.mem_map, m12CoverNormTabs, m12CoverRepTabs]
      refine ⟨_, ⟨n, hn, rfl⟩, _, ⟨r', hr', rfl⟩, ?_⟩
      have h1 := Rep.compT (rep_toTable (by norm_num) n)
        (Rep.compT (rep_toTable (by norm_num) r'.1) (rep_toTable (by norm_num) n⁻¹))
      have h2 := Rep.powT (by norm_num) hT (i - 1 + 1)
      have h3 : g ^ (i - 1 + 1) = n * (r'.1 * n⁻¹) := by
        rw [Nat.sub_add_cancel hi1, hgi, mul_assoc]
      have h4 : powT 12 (i - 1 + 1) T = compT 12 T (powT 12 (i - 1) T) := rfl
      rw [h3, h4] at h2
      rw [h4]
      exact compT_ext h1 h2
    rw [hcov]
    simp
  · have h5 : ordTest 12 5 T = false := by
      cases h : ordTest 12 5 T
      · rfl
      · exact absurd (Or.inl ((ordTest_iff perm_faithful hT (by norm_num)).1 h)) ho
    have h11 : ordTest 12 11 T = false := by
      cases h : ordTest 12 11 T
      · rfl
      · exact absurd (Or.inr ((ordTest_iff perm_faithful hT (by norm_num)).1 h)) ho
    rw [h5, h11]
    rfl

theorem cover_ok :
    countProducts 12 m12CoverBad (levelTables m12Certificate) (idT 12) = 0 :=
  CFSG.KC.L52I.countProducts_eq_zero_of (by norm_num) m12Certificate m12Certificate_check
    fun x T hT => bad_false (m12Certificate_originalSubgroup ▸ x.2) hT

end CertificateChecks.KernelSporSch.M12Cover9681

end
