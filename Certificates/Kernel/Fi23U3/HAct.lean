module

public import Certificates.Kernel.Fi23U3.HCard
public import Certificates.Kernel.Fi23U3.Dce.Index

public section

namespace CFSG.KD.Fi23H

open CFSG.CosetTable CFSG.KD.Fi23Dce3 CFSG.KC.TwDce2 CFSG.Certificates.TwDce
  CFSG.Certificates.CosetEnumeration CFSG.KC.YModel

@[expose] def cd (j : Fin 3) : ℕ := [2, 0, 4].getD j.val 0

@[expose] def code (l : Fin 3 × Bool) : ℕ := cd l.1 + if l.2 then 0 else 1

@[expose] def rhCodes : List (List ℕ) := rhW.map (List.map code)

theorem rh_ok : CFSG.KC.TwDce3.relsOK PB F 54 rhCodes = true := by
  quickRfl

theorem rh_len_bool : (rhCodes.all fun w => decide (w.length < 2 ^ 32)) = true := by
  quickRfl

theorem rh_fix : ∀ w ∈ rhCodes, (∀ c ∈ w, c < 12) ∧
    ∀ p < 54, w.foldl (fun q c => fieldAt PB (F c) q) p = p :=
  CFSG.Certificates.TwDce3.relsOK_sound rh_ok fun w hw => by
    simpa using List.all_eq_true.1 rh_len_bool w hw

@[expose] def qGen (c : ℕ) : Fin 3 := ⟨[1, 0, 2].getD (c / 2) 0 % 3, Nat.mod_lt _ (by norm_num)⟩

theorem cd_facts : ∀ j : Fin 3, cd j < 6 ∧ cd j % 2 = 0 ∧ qGen (cd j) = j ∧
    ivL INVM (cd j) = cd j + 1 ∧ ivL INVM (cd j + 1) = cd j := by
  decide +kernel

theorem qGen_facts : ∀ c < 6, (c % 2 = 0 → cd (qGen c) = c) ∧ (c % 2 = 1 → cd (qGen c) + 1 = c) ∧
    (subsetOf 4 [0, 1, 2]).get (qGen c) = fiHGen c := by
  decide +kernel

@[expose] noncomputable def xq (c : ℕ) : PG 3 rhW :=
  if c < 6 then (if c % 2 = 0 then PresentedGroup.of (qGen c) else (PresentedGroup.of (qGen c))⁻¹)
  else 1

theorem qGen_congr {d e : ℕ} (h : d / 2 = e / 2) : qGen d = qGen e := by
  simp only [qGen, h]

theorem xq_inv : ∀ c < 12, xq (ivL INVM c) = (xq c)⁻¹ := by
  intro c hc
  rw [inv_eq c hc]
  by_cases h6 : c < 6
  · rw [if_pos h6]
    by_cases h : c % 2 = 0
    · rw [if_pos h]
      simp only [xq, if_pos h6, if_pos (show c + 1 < 6 by omega), if_pos h,
        if_neg (show ¬ (c + 1) % 2 = 0 by omega), qGen_congr (show (c + 1) / 2 = c / 2 by omega)]
    · rw [if_neg h]
      simp only [xq, if_pos h6, if_pos (show c - 1 < 6 by omega), if_neg h,
        if_pos (show (c - 1) % 2 = 0 by omega), inv_inv,
        qGen_congr (show (c - 1) / 2 = c / 2 by omega)]
  · rw [if_neg h6]
    simp [xq, h6]

@[expose] noncomputable def tab (c p : ℕ) : ℕ := if p < 54 then fieldAt PB (F c) p else p

theorem tab_inv {c : ℕ} (hc : c < 12) (p : ℕ) : tab (ivL INVM c) (tab c p) = p := by
  by_cases hp : p < 54
  · have h1 := f_lt c hc p hp
    have hi := ivL_lt hc
    simp only [tab, if_pos hp, if_pos h1]
    rw [← fb_eq _ hi _ h1, ← fb_eq c hc p hp]
    exact ((CFSG.Certificates.TwDce2.Rels.lettersOK_sound fb_ok.1 c hc).2 p hp).2
  · simp only [tab, if_neg hp]

@[expose] noncomputable def permJ (j : Fin 3) : Equiv.Perm ℕ where
  toFun := tab (cd j)
  invFun := tab (cd j + 1)
  left_inv p := by
    have h := tab_inv (c := cd j) (by have := (cd_facts j).1; omega) p
    rwa [(cd_facts j).2.2.2.1] at h
  right_inv p := by
    have h := tab_inv (c := cd j + 1) (by have := (cd_facts j).1; omega) p
    rwa [(cd_facts j).2.2.2.2] at h

theorem lift_unop (w : List (Fin 3 × Bool)) (p : ℕ) :
    (FreeGroup.lift (fun j => MulOpposite.op (permJ j)) (FreeGroup.mk w)).unop p =
      w.foldl (fun q l => tab (code l) q) p := by
  induction w generalizing p with
  | nil => rfl
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul,
      MulOpposite.unop_mul, Equiv.Perm.mul_apply, List.foldl_cons, ← ih]
    congr 1
    obtain ⟨j, b⟩ := l
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv,
        FreeGroup.lift_apply_of, MulOpposite.unop_inv, MulOpposite.unop_op]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl, FreeGroup.lift_apply_of,
        MulOpposite.unop_op]
      simp [permJ, code]

theorem foldl_tab : ∀ (w : List ℕ), (∀ c ∈ w, c < 12) → ∀ p,
    w.foldl (fun q c => tab c q) p =
      if p < 54 then w.foldl (fun q c => fieldAt PB (F c) q) p else p
  | [], _, p => by split_ifs <;> rfl
  | c :: w, hw, p => by
    have hc := hw c List.mem_cons_self
    have hw' : ∀ d ∈ w, d < 12 := fun d hd => hw d (List.mem_cons_of_mem _ hd)
    rw [List.foldl_cons, List.foldl_cons, foldl_tab w hw']
    by_cases hp : p < 54
    · simp only [tab, if_pos hp, if_pos (f_lt c hc p hp)]
    · simp only [tab, if_neg hp]

theorem rels_perm : ∀ r ∈ {r : FreeGroup (Fin 3) | r ∈ rhW.map FreeGroup.mk},
    FreeGroup.lift (fun j => MulOpposite.op (permJ j)) r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  have hm : w.map code ∈ rhCodes := List.mem_map_of_mem hw
  obtain ⟨hlt, hfix⟩ := rh_fix _ hm
  apply MulOpposite.unop_injective
  ext p
  have e : w.foldl (fun q l => tab (code l) q) p = (w.map code).foldl (fun q c => tab c q) p := by
    rw [List.foldl_map]
  rw [lift_unop, MulOpposite.unop_one, Equiv.Perm.one_apply, e, foldl_tab _ hlt p]
  split_ifs with hp
  · exact hfix p hp
  · rfl

@[expose] noncomputable def ρ : PG 3 rhW →* (Equiv.Perm ℕ)ᵐᵒᵖ := PresentedGroup.toGroup rels_perm

theorem ρ_of (j : Fin 3) : ρ (PresentedGroup.of j) = MulOpposite.op (permJ j) :=
  PresentedGroup.toGroup.of rels_perm

theorem xq_cd (j : Fin 3) : xq (cd j) = PresentedGroup.of j := by
  obtain ⟨h6, h2, hq, -⟩ := cd_facts j
  simp only [xq, if_pos h6, if_pos h2, hq]

theorem xq_gen (q : PG 3 rhW) : ∃ w : List ℕ, (∀ c ∈ w, c < 12) ∧ q = evalWord xq w := by
  have hq : q ∈ (⊤ : Subgroup (PG 3 rhW)) := Subgroup.mem_top q
  rw [← PresentedGroup.closure_range_of] at hq
  induction hq using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨[cd j], fun c hc => ?_, ?_⟩
    · rw [List.mem_singleton.1 hc]
      have := (cd_facts j).1
      omega
    · simp [evalWord, xq_cd]
  | one => exact ⟨[], by simp, by simp [evalWord]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    refine ⟨u ++ v, fun c hc => ?_, by simp [evalWord]⟩
    rcases List.mem_append.1 hc with hc | hc
    · exact hu c hc
    · exact hv c hc
  | inv x _ hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨u.reverse.map (ivL INVM), fun c hc => ?_, ?_⟩
    · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      exact ivL_lt (hu d (List.mem_reverse.1 hd))
    · exact (evalWord_rev_inv fun c hc => xq_inv c (hu c hc)).symm

noncomputable def hact : HAct (PG 3 rhW) where
  π := toPC
  xq := xq
  π_xq c hc := by
    by_cases h6 : c < 6
    · have hg := (qGen_facts c h6).2.2
      simp only [xq, fiX, if_pos h6]
      split_ifs
      · rw [toPC_of, gen, hg]
      · rw [map_inv, toPC_of, gen, hg]
    · simp only [xq, fiX, if_neg h6, map_one]
  xq_inv := xq_inv
  gen := xq_gen
  pt q p := (ρ q).unop p
  pt_one p := by simp
  pt_mul a b p := by simp [Equiv.Perm.mul_apply]
  pt_xq c hc p hp := by
    by_cases h6 : c < 6
    · obtain ⟨he, ho, -⟩ := qGen_facts c h6
      simp only [xq, if_pos h6]
      split_ifs with h
      · rw [ρ_of, MulOpposite.unop_op]
        change tab (cd (qGen c)) p = _
        rw [he h, tab, if_pos hp]
      · rw [map_inv, ρ_of, MulOpposite.unop_inv, MulOpposite.unop_op]
        change tab (cd (qGen c) + 1) p = _
        rw [ho (by omega), tab, if_pos hp]
    · simp only [xq, if_neg h6, map_one, MulOpposite.unop_one, Equiv.Perm.one_apply]
      exact (f_id hc (by omega) hp).symm

theorem card_fiPC : Finite fiPC ∧ Nat.card fiPC ≤ 6377292 := by
  have := card_rhW.1
  exact hact.card_fiPC_le card_rhW.2

end CFSG.KD.Fi23H

end
