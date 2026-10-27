module

public import Certificates.Kernel.G23F48.A23Glue
public import CFSG.Milestones.ASVolI.F48.Rest.G23Defs
public import Certificates.Kernel.G23F48.A24Glue

public section

set_option maxRecDepth 400000

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KD.G23A22
open CFSG.Sporadic.HNOddCore (arrGen)
open MulAction

theorem sigma_mem_X {i : ℕ} (hi : i < 4) : burnsideF48t_g23σ i ∈ burnsideF48t_g23X :=
  letter_mem hi

theorem tauConj_mem_X {i : ℕ} (hi : i < 4) :
    burnsideF48t_g23τ * burnsideF48t_g23γ i * burnsideF48t_g23τ⁻¹ ∈ burnsideF48t_g23X :=
  tau_conj_mem hi

theorem rels_hold : ∀ r ∈ burnsideF48t_g23R1 ++ burnsideF48t_g23R2 ++
    [(List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten],
    burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_g23σ i) r = 1 := by
  intro r hr
  have hp := prep_evP (n := 728) (w := 10) (LP := LP) (LPI := LPI)
    (σ := fun i : Fin 4 => sig i) (by norm_num) (by norm_num)
    (fun i => ⟨(prep_letter i.2).2.1, (prep_letter i.2).2.2⟩) r
  rw [Nat.eq_of_beq_eq_true (List.all_eq_true.1 rel_ok r hr)] at hp
  exact oprep_unique hp (Orb.prep_pidn (by norm_num) (by norm_num))

theorem kap_eq_kappa {j : ℕ} (hj : j < 2) : kap j = burnsideF48t_g23κ j := by
  have hl : burnsideF48t_g23KW.length = 2 := by simp [burnsideF48t_g23KW]
  rw [kap, kArr_eq, getElem!_map_toArray [] (by omega)]
  exact onPermOfArr_eq (burnsideF48t_prep_evA recL _)

theorem prep_xy : Orb.PRep 728 10 (pcomp 728 10 (mask 10) (LP 2) (LP 3)) (sig 2 * sig 3) :=
  Orb.prep_pcomp (by norm_num) (prep_letter (by norm_num)).2.1 (prep_letter (by norm_num)).2.1

theorem comm_ne {k : ℕ} {c : Equiv.Perm (Fin 728)} (hc : Orb.PRep 728 10 k c)
    (h : Nat.beq (pcomp 728 10 (mask 10) (pcomp 728 10 (mask 10) (LP 2) (LP 3)) k)
      (pcomp 728 10 (mask 10) k (pcomp 728 10 (mask 10) (LP 2) (LP 3))) = false) :
    ¬ (sig 2 * sig 3 * c = c * (sig 2 * sig 3)) :=
  ne_of_pack (PF.pcomp_shr _ _ (by norm_num) (by norm_num))
    (PF.pcomp_shr _ _ (by norm_num) (by norm_num)) (Orb.prep_pcomp (by norm_num) prep_xy hc)
    (Orb.prep_pcomp (by norm_num) hc prep_xy) h

theorem comm_xy :
    ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 0 =
        burnsideF48t_g23κ 0 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
    ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * burnsideF48t_g23κ 1 =
        burnsideF48t_g23κ 1 * (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) ∧
    ¬ (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3 * (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) =
        (burnsideF48t_g23κ 0 * burnsideF48t_g23κ 1) *
          (burnsideF48t_g23σ 2 * burnsideF48t_g23σ 3)) := by
  have h := comm_ok
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨h0, h1, h2⟩ := h
  rw [← kap_eq_kappa (j := 0) (by norm_num), ← kap_eq_kappa (j := 1) (by norm_num)]
  exact ⟨comm_ne (prep_kap (by norm_num)).2 h0, comm_ne (prep_kap (by norm_num)).2 h1,
    comm_ne prep_k01 h2⟩

theorem sig_eq (i : ℕ) : sig i = burnsideF48t_g23σ i := rfl

theorem tau_eq : tau = burnsideF48t_g23τ := rfl

theorem fin0 : (0 : Fin 728) = ⟨0, by norm_num⟩ := rfl

theorem fin364 : (364 : Fin 728) = ⟨364, by norm_num⟩ := rfl

theorem tau_zero_ge : 364 ≤ ((burnsideF48t_g23τ 0 : Fin 728) : ℕ) := by
  rw [← tau_eq, ← prep_tau.2.1 0]
  exact tau_0.1

theorem sig_fixes {i : ℕ} (hi : i < 4) {p : ℕ} (hp : p < 728)
    (h : pg 10 (mask 10) (LP i) p = p) : sig i ⟨p, hp⟩ = ⟨p, hp⟩ :=
  Fin.ext ((sig_apply hi ⟨p, hp⟩).trans h)

theorem sig_moves {i : ℕ} (hi : i < 4) {p : ℕ} (hp : p < 728)
    (h : pg 10 (mask 10) (LP i) p ≠ p) : sig i ⟨p, hp⟩ ≠ ⟨p, hp⟩ :=
  fun he => h ((sig_apply hi ⟨p, hp⟩).symm.trans (congrArg Fin.val he))

theorem sig_moves' {i : ℕ} (hi : i < 4) {p : Fin 728} (h : pg 10 (mask 10) (LP i) p ≠ p) :
    sig i p ≠ p :=
  fun he => h ((sig_apply hi p).symm.trans (congrArg Fin.val he))

theorem letters_fix :
    burnsideF48t_g23σ 0 0 = 0 ∧ burnsideF48t_g23σ 0 364 = 364 ∧
    burnsideF48t_g23σ 1 0 = 0 ∧ burnsideF48t_g23σ 1 364 = 364 ∧
    burnsideF48t_g23σ 2 0 = 0 ∧ burnsideF48t_g23σ 3 364 = 364 ∧
    burnsideF48t_g23σ 3 0 ≠ 0 ∧ burnsideF48t_g23σ 2 364 ≠ 364 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, -⟩ := fix_ok
  rw [← sig_eq 0, ← sig_eq 1, ← sig_eq 2, ← sig_eq 3, fin0, fin364]
  exact ⟨sig_fixes (i := 0) (by norm_num) _ f1, sig_fixes (i := 0) (by norm_num) _ f2,
    sig_fixes (i := 1) (by norm_num) _ f3, sig_fixes (i := 1) (by norm_num) _ f4,
    sig_fixes (i := 2) (by norm_num) _ f5, sig_fixes (i := 3) (by norm_num) _ f6,
    sig_moves (i := 3) (by norm_num) _ f7, sig_moves (i := 2) (by norm_num) _ f8⟩

theorem s0g_fixes {j : ℕ} (hj : j < 3) {p : Fin 728} (h : pg 10 (mask 10) (S0C.S j) p = p) :
    s0g j ∈ stabilizer (Equiv.Perm (Fin 728)) p := by
  rw [mem_stabilizer_iff, Equiv.Perm.smul_def]
  exact Fin.ext (((prep_s0g hj).2.1 p).symm.trans h)

theorem S0_le_stab : burnsideF48t_g23S0' ≤ stabilizer (Equiv.Perm (Fin 728)) (0 : Fin 728) ⊓
    stabilizer (Equiv.Perm (Fin 728)) (364 : Fin 728) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := fix_ok
  rw [burnsideF48t_g23S0', arrGen, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk3 : k < 3 := by
    rw [s0Arr_get.1] at hk
    exact hk
  rw [CFSG.Sporadic.HNOddCore.permOfArr_eq_of_prep (prep_s0g hk3).1]
  have h := allN_spec h9 k hk3
  simp only [Bool.and_eq_true] at h
  exact Subgroup.mem_inf.2 ⟨s0g_fixes hk3 (Nat.eq_of_beq_eq_true h.1),
    s0g_fixes hk3 (Nat.eq_of_beq_eq_true h.2)⟩

theorem S0_fix {s : Equiv.Perm (Fin 728)} (hs : s ∈ burnsideF48t_g23S0') :
    s 0 = 0 ∧ s 364 = 364 := by
  have h := Subgroup.mem_inf.1 (S0_le_stab hs)
  rw [mem_stabilizer_iff, mem_stabilizer_iff] at h
  exact h

theorem S0_moves {p : Fin 728} (h0 : p ≠ 0) (h364 : p ≠ 364) :
    ∃ s ∈ burnsideF48t_g23S0', s p ≠ p := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := fix_ok
  have h := allN_spec h10 p p.2
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.not_eq_true',
    Nat.beq_eq_true_eq] at h
  have hp0 : (p : ℕ) ≠ 0 := fun e => h0 (Fin.ext e)
  have hp364 : (p : ℕ) ≠ 364 := fun e => h364 (Fin.ext e)
  have hj : ∃ j < 3, Nat.beq (pg 10 (mask 10) (S0C.S j) p) p = false := by
    rcases h with (e | e) | e | e | e
    · exact absurd (Nat.eq_of_beq_eq_true e) hp0
    · exact absurd (Nat.eq_of_beq_eq_true e) hp364
    · exact ⟨0, by norm_num, e⟩
    · exact ⟨1, by norm_num, e⟩
    · exact ⟨2, by norm_num, e⟩
  obtain ⟨j, hj3, e⟩ := hj
  refine ⟨s0g j, s0g_mem hj3, fun he => Nat.ne_of_beq_eq_false e ?_⟩
  exact ((prep_s0g hj3).2.1 p).trans (congrArg Fin.val he)

theorem P1_moves {p : Fin 728} (hp : 364 ≤ (p : ℕ)) : ∃ g ∈ burnsideF48t_g23P1', g p ≠ p := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := fix_ok
  have h := allN_spec h11 ((p : ℕ) - 364) (by omega)
  rw [Nat.sub_add_cancel hp] at h
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.not_eq_true']
    at h
  rcases h with e | e | e
  · exact ⟨sig 0, sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num),
      sig_moves' (by norm_num) (Nat.ne_of_beq_eq_false e)⟩
  · exact ⟨sig 1, sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num),
      sig_moves' (by norm_num) (Nat.ne_of_beq_eq_false e)⟩
  · exact ⟨sig 2, sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num),
      sig_moves' (by norm_num) (Nat.ne_of_beq_eq_false e)⟩

theorem P2_moves {p : Fin 728} (hp : (p : ℕ) < 364) : ∃ g ∈ burnsideF48t_g23P2', g p ≠ p := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12⟩ := fix_ok
  have h := allN_spec h12 p hp
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, Bool.not_eq_true']
    at h
  rcases h with e | e | e
  · exact ⟨sig 0, sig_mem_arrGen (k := 0) (by decide) rfl (by norm_num),
      sig_moves' (by norm_num) (Nat.ne_of_beq_eq_false e)⟩
  · exact ⟨sig 1, sig_mem_arrGen (k := 1) (by decide) rfl (by norm_num),
      sig_moves' (by norm_num) (Nat.ne_of_beq_eq_false e)⟩
  · exact ⟨sig 3, sig_mem_arrGen (k := 2) (by decide) rfl (by norm_num),
      sig_moves' (by norm_num) (Nat.ne_of_beq_eq_false e)⟩

end CFSG.KC.G23F48

end
