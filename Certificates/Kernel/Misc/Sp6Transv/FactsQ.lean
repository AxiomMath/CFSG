module

public import Certificates.Kernel.Misc.Sp6Transv.Facts
import CFSG.Certificates.Kernel.Misc.PermClosProof

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.Sp6Transv.Facts

open CFSG.KC.Misc.Sp6Transv CFSG.KC.Misc.Clos CFSG.KD.Sp62 CFSG.KC.Sp62
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
open CertificateChecks.KernelMisc.Sp6Transv

variable {z : Fin 3 → H6} {t s f0 f2 : H6} {q : Fin 5 → H6}

theorem range_q : {g | g ∈ [q 0, q 1, q 2, q 3, q 4]} = Set.range q := by
  ext g
  simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩]
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp

theorem Hyp.Q_facts (H : Hyp z t s f0 f2 q) :
    (∀ k < 32, ∃ g ∈ Subgroup.closure (Set.range q), enc6 g = EQ k) ∧
      Nat.card (Subgroup.closure (Set.range q)) = 32 ∧
      ∀ g ∈ Subgroup.closure (Set.range q), ∃ k < 32, enc6 g = EQ k := by
  obtain ⟨h1, -, h3⟩ := clos_card_proved enc6_enc [q 0, q 1, q 2, q 3, q 4] H.eq (by norm_num)
    q_parts.1 q_parts.2.1
  obtain ⟨h4, h5⟩ := h3 q_parts.2.2.1
  rw [range_q] at h1 h4 h5
  exact ⟨h1, h4, h5⟩

theorem Q_dist : ∀ i < 32, ∀ j < 32, EQ i = EQ j → i = j :=
  sort_distinct_proved q_parts.2.1

theorem Hyp.eqi (H : Hyp z t s f0 f2 q) (i : Fin 5) : enc6 (q i) = QG i := by
  have h := H.eq i i.2
  fin_cases i <;> exact h.symm

theorem Hyp.Q_le (H : Hyp z t s f0 f2 q) :
    Subgroup.closure (Set.range q) ≤ Subgroup.centralizer ({s} : Set H6) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  refine eq_of_enc ?_
  rw [emul, emul, H.es, H.eqi]
  fin_cases i <;> decide +kernel

theorem abel_parts : ∀ i < 32, MULF (EQ i) (EQ i) = ONE ∧ ∀ j < 32, commF (EQ i) (EQ j) = true := by
  intro i hi
  have h := (allN_iff _ _).1 q_parts.2.2.2.1 i hi
  obtain ⟨h1, h2⟩ := andB_eq_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, (allN_iff _ _).1 h2⟩

theorem commF_iff (g h : H6) :
    commF (enc6 g) (enc6 h) = true ↔ g ∈ Subgroup.centralizer ({h} : Set H6) := by
  rw [Subgroup.mem_centralizer_singleton_iff, commF, Nat.beq_eq, ← emul, ← emul]
  exact ⟨fun e => eq_of_enc e, fun e => by rw [e]⟩

theorem Hyp.Q_comm (H : Hyp z t s f0 f2 q) :
    ∀ x ∈ Subgroup.closure (Set.range q), ∀ y ∈ Subgroup.closure (Set.range q),
      x * y = y * x := by
  intro x hx y hy
  obtain ⟨i, hi, ei⟩ := H.Q_facts.2.2 x hx
  obtain ⟨j, hj, ej⟩ := H.Q_facts.2.2 y hy
  have h := (abel_parts i hi).2 j hj
  rw [← ei, ← ej, commF_iff, Subgroup.mem_centralizer_singleton_iff] at h
  exact h

theorem Hyp.Q_sq (H : Hyp z t s f0 f2 q) :
    ∀ x ∈ Subgroup.closure (Set.range q), x * x = 1 := by
  intro x hx
  obtain ⟨i, hi, ei⟩ := H.Q_facts.2.2 x hx
  exact eq_of_enc (by rw [emul, ei, enc_one]; exact (abel_parts i hi).1)

theorem count_parts : cntR 32 (fun i => commF (EQ i) (KS 1)) = 8 ∧
    cntR 32 (fun i => commF (EQ i) (KS 3)) = 8 ∧
    cntR 32 (fun i => CFSG.KC.Ord.andB (commF (EQ i) (KS 1)) (commF (EQ i) (KS 3))) = 2 ∧
    cntR 32 (fun i => commF (EQ i) (MULF (KS 1) (KS 3))) = 2 ∧
    cntR 32 (fun i => commF (EQ i) (MULF (KS 1) (MULF (KS 3) (KS 3)))) = 2 := by
  have h := q_parts.2.2.2.2.1
  unfold countQ at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  obtain ⟨h4, h5⟩ := andB_eq_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem Hyp.card_Q_cen (H : Hyp z t s f0 f2 q) {x : H6} {X : ℕ} (hx : enc6 x = X) :
    Nat.card ↥(Subgroup.closure (Set.range q) ⊓ Subgroup.centralizer ({x} : Set H6)) =
      cntR 32 (fun i => commF (EQ i) X) := by
  refine card_inf_of_cnt H.Q_facts.1 H.Q_facts.2.2 Q_dist fun k _ g hg => ?_
  rw [← hg, ← hx, commF_iff]

theorem Hyp.counts (H : Hyp z t s f0 f2 q) :
    Nat.card ↥(Subgroup.closure (Set.range q) ⊓ Subgroup.centralizer ({z 0} : Set H6)) = 8 ∧
    Nat.card ↥(Subgroup.closure (Set.range q) ⊓ Subgroup.centralizer ({z 2} : Set H6)) = 8 ∧
    Nat.card ↥(Subgroup.closure (Set.range q) ⊓ Subgroup.centralizer ({z 0} : Set H6) ⊓
      Subgroup.centralizer ({z 2} : Set H6)) = 2 ∧
    Nat.card ↥(Subgroup.closure (Set.range q) ⊓ Subgroup.centralizer ({z 0 * z 2} : Set H6)) = 2 ∧
    Nat.card ↥(Subgroup.closure (Set.range q) ⊓
      Subgroup.centralizer ({z 0 * z 2 ^ 2} : Set H6)) = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [H.card_Q_cen H.ez0, count_parts.1]
  · rw [H.card_Q_cen H.ez2, count_parts.2.1]
  · rw [inf_assoc]
    refine (card_inf_of_cnt H.Q_facts.1 H.Q_facts.2.2 Q_dist fun k _ g hg => ?_).trans
      count_parts.2.2.1
    rw [Subgroup.mem_inf, ← commF_iff, ← commF_iff, hg, H.ez0, H.ez2]
    exact ⟨fun h => andB_eq_true h, fun ⟨h1, h2⟩ => by rw [h1, h2]; rfl⟩
  · rw [H.card_Q_cen (by rw [emul, H.ez0, H.ez2]), count_parts.2.2.2.1]
  · rw [H.card_Q_cen (by rw [sq, emul, emul, H.ez0, H.ez2]), count_parts.2.2.2.2]

theorem wit_num : MULF (MULF (MULF (MULF (QG 0) (KS 5)) (QG 0)) (KS 7))
    (MULF (MULF (MULF (QG 1) (PW (KS 6) 3)) (QG 1)) (PW (KS 8) 3)) = KS 0 := by
  decide +kernel

theorem Hyp.mem_commutator (H : Hyp z t s f0 f2 q) :
    s ∈ ⁅Subgroup.closure (Set.range q), Subgroup.centralizer ({s} : Set H6)⁆ := by
  have hq : ∀ i, q i ∈ Subgroup.closure (Set.range q) := fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have i0 : (q 0)⁻¹ = q 0 := inv_eq_of_mul_eq_one_right (H.Q_sq _ (hq 0))
  have i1 : (q 1)⁻¹ = q 1 := inv_eq_of_mul_eq_one_right (H.Q_sq _ (hq 1))
  have hc2 : cs1 ^ 3 ∈ Subgroup.centralizer ({s} : Set H6) := pow_mem H.cs1_mem 3
  have h1 := Subgroup.commutator_mem_commutator (hq 0) H.cs0_mem
  have h2 := Subgroup.commutator_mem_commutator (hq 1) hc2
  rw [commutatorElement_def] at h1 h2
  have e : s = q 0 * cs0 * (q 0)⁻¹ * cs0⁻¹ * (q 1 * cs1 ^ 3 * (q 1)⁻¹ * (cs1 ^ 3)⁻¹) := by
    rw [i0, i1, ← inv_pow]
    refine eq_of_enc ?_
    rw [H.es, emul, emul, emul, emul, emul, emul, emul, enc6_pow, enc6_pow, H.eqi 0, H.eqi 1,
      enc_cs0.1, enc_cs0.2, enc_cs1.1, enc_cs1.2]
    exact wit_num.symm
  have h3 := mul_mem h1 h2
  rwa [← e] at h3

end CertificateChecks.KernelMisc.Sp6Transv.Facts

end
