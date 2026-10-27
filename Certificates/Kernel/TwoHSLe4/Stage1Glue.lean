module

public import Certificates.Kernel.TwoHSLe4.SO5Eq
public import Certificates.Kernel.TwoHSLe4.Stage1A
public import Certificates.Kernel.TwoHSLe4.Stage1B
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem reps_eq (i : Fin 4) : pgRepsC i = unpk (SG i.val) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := sg_eq
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem mem_p0 {p : ℕ} (h : p ∈ P0L) : unpk p ∈ pgP0Code := by
  rw [p0_eq]
  exact List.mem_map_of_mem h

theorem p0_cases {a : FM} (ha : a ∈ pgP0Code) : ∃ p ∈ P0L, a = unpk p := by
  rw [p0_eq] at ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ha
  exact ⟨p, hp, rfl⟩

theorem stage1 : PGStage1F := by
  refine ⟨a_len, a_nodup, a_so, a_one, ?_, ?_, a_reps, ?_, ?_, ?_, a_x15, a_x13, a_f2⟩
  · intro a ha b hb
    obtain ⟨p, hp, rfl⟩ := p0_cases ha
    obtain ⟨q, hq, rfl⟩ := p0_cases hb
    rw [fmMul_unpk]
    refine mem_p0 ?_
    have h := List.all_eq_true.1 (List.all_eq_true.1 b_mul p hp) q hq
    simpa using h
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := p0_cases ha
    obtain ⟨q, hq, hpq⟩ := List.any_eq_true.1 (List.all_eq_true.1 b_inv p hp)
    exact ⟨unpk q, mem_p0 hq, (fmMul_eq_one_iff p q).2 (beq_iff_eq.1 hpq)⟩
  · intro a ha haa
    obtain ⟨p, hp, rfl⟩ := p0_cases ha
    have h := List.all_eq_true.1 b_inv2 p hp
    have hpp : (mulK p p == oneK) = true := beq_iff_eq.2 ((fmMul_eq_one_iff p p).1 haa)
    rw [hpp] at h
    simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
      List.any_eq_true, beq_iff_eq] at h
    rcases h with h | ⟨e, he, rfl⟩
    · exact Or.inl h
    · refine Or.inr ⟨(unpk e.1, unpk e.2.1, ⟨e.2.2 % 4, Nat.mod_lt _ (by norm_num)⟩), ?_, rfl⟩
      rw [cj_eq]
      exact List.mem_map_of_mem he
  · intro e he
    rw [cj_eq] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
    have h := List.all_eq_true.1 b_cj e' he'
    simp only [Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at h
    have hso := a_cj _ (by rw [cj_eq]; exact List.mem_map_of_mem he')
    refine ⟨mem_p0 h.1, hso.1, hso.2, ?_⟩
    change fmMul (unpk e'.2.1) (unpk e'.1) =
      fmMul (pgRepsC ⟨e'.2.2 % 4, Nat.mod_lt _ (by norm_num)⟩) (unpk e'.2.1)
    rw [reps_eq, fmMul_unpk, fmMul_unpk, h.2]
  · intro a ha
    obtain ⟨p, hp, rfl⟩ := p0_cases ha
    rw [sg_eq.2.2.1, fmMul_unpk, fmMul_unpk, beq_iff_eq.1 (List.all_eq_true.1 b_tau3 p hp)]

end CertificateChecks.KernelTwoHSLe4.SO5

end
