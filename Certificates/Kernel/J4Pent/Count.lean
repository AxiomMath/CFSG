module

public import Certificates.Kernel.J4Pent.Lanes

public section

namespace CertificateChecks.KernelJ4Pent

open CFSG.KC.J4Pent CFSG.KD.J4Pent CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop

theorem nadd (a b : Nat) : Nat.add a b = a + b := rfl

@[expose] def LexLt (p q : Nat × Nat) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem lexLt_trans {p q r : Nat × Nat} (h1 : LexLt p q) (h2 : LexLt q r) : LexLt p r := by
  unfold LexLt at *
  omega

theorem pairLt_eq (p q : Nat × Nat) : pairLt p q = true ↔ LexLt p q := by
  unfold pairLt LexLt
  rw [bIf_eq, bAnd_eq]
  by_cases hlt : p.1 < q.1
  · have e : Nat.blt p.1 q.1 = true := by rw [Nat.blt_eq]; exact hlt
    rw [e]
    simp [hlt]
  · have e : Nat.blt p.1 q.1 = false := by
      cases h : Nat.blt p.1 q.1
      · rfl
      · rw [Nat.blt_eq] at h
        exact absurd h hlt
    rw [e]
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq]
    constructor
    · intro h'
      exact Or.inr h'
    · rintro (h' | h')
      · exact absurd h' hlt
      · exact h'

theorem incrP_some : ∀ (L : List (Nat × Nat)) (q : Nat × Nat), incrP L (some q) = true →
    (q :: L).Pairwise LexLt
  | [], q, _ => List.pairwise_singleton _ _
  | p :: L, q, h => by
    change bAnd(pairLt q p, incrP L (some p)) = true at h
    rw [bAnd_eq, Bool.and_eq_true, pairLt_eq] at h
    have ih := incrP_some L p h.2
    refine List.Pairwise.cons ?_ ih
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact lexLt_trans h.1 (List.rel_of_pairwise_cons ih hx)

theorem incrP_none : ∀ (L : List (Nat × Nat)), incrP L none = true → L.Pairwise LexLt
  | [], _ => List.Pairwise.nil
  | p :: L, h => incrP_some L p h

theorem memN_iff (n : Nat) (L : List Nat) : memN n L = true ↔ n ∈ L := by
  unfold memN
  rw [anyB_eq, List.any_eq_true]
  simp [Nat.beq_eq]

@[expose] noncomputable def blockSum (B : List (List Nat × List Nat)) : Nat :=
  (B.map fun p => p.1.length).sum

noncomputable def blkK (blk : List (List Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ ih2 => strictN ih2 fun r2 => Nat.add r2 (lenK p.1)) blk

noncomputable def totK (T : List (List (List Nat × List Nat))) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun blk _ ih => strictN ih fun r => Nat.add r (blkK blk)) T

theorem blkK_eq : ∀ blk : List (List Nat × List Nat), blkK blk = blockSum blk
  | [] => rfl
  | p :: blk => by
    have e : blkK (p :: blk) = strictN (blkK blk) fun r2 => Nat.add r2 (lenK p.1) := rfl
    rw [e, strictN_eq, blkK_eq blk, lenK_eq]
    unfold blockSum
    rw [List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

theorem totK_eq : ∀ T : List (List (List Nat × List Nat)), totK T = (T.map blockSum).sum
  | [] => rfl
  | blk :: T => by
    have e : totK (blk :: T) = strictN (totK T) fun r => Nat.add r (blkK blk) := rfl
    rw [e, strictN_eq, totK_eq T, blkK_eq, List.map_cons, List.sum_cons]
    exact Nat.add_comm _ _

theorem fixTotal_eq : fixTotal = (TB.map blockSum).sum := totK_eq TB

theorem complete_of_card {F : List (Nat × Nat)} {T : Nat → List Nat} {n total : Nat}
    (hnd : F.Nodup) (hmem : ∀ p ∈ F, p.1 ∈ T p.2 ∧ 0 < p.2 ∧ p.2 < n) (hlen : F.length = total)
    (hsum : ∑ t ∈ Finset.range n, (T t).length ≤ total) {l t : Nat} (ht0 : 0 < t) (ht : t < n)
    (h : l ∈ T t) : (l, t) ∈ F := by
  classical
  let S : Finset (Nat × Nat) := ((Finset.range n).filter (fun t => 0 < t)).biUnion
    fun t => ((T t).toFinset).image fun l => (l, t)
  have hsub : F.toFinset ⊆ S := by
    intro p hp
    rw [List.mem_toFinset] at hp
    have h1 := (hmem p hp).1
    have h2 := (hmem p hp).2
    exact Finset.mem_biUnion.2 ⟨p.2, Finset.mem_filter.2 ⟨Finset.mem_range.2 h2.2, h2.1⟩,
      Finset.mem_image.2 ⟨p.1, List.mem_toFinset.2 h1, rfl⟩⟩
  have hS : S.card ≤ total := by
    calc S.card ≤ ∑ t ∈ (Finset.range n).filter (fun t => 0 < t),
          (((T t).toFinset).image fun l => (l, t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ (Finset.range n).filter (fun t => 0 < t), (T t).length :=
          Finset.sum_le_sum fun t _ => Finset.card_image_le.trans (List.toFinset_card_le _)
      _ ≤ ∑ t ∈ Finset.range n, (T t).length :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ total := hsum
  have hcard : F.toFinset.card = total := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : F.toFinset = S := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hS)
  have hin : (l, t) ∈ S := Finset.mem_biUnion.2 ⟨t, Finset.mem_filter.2
    ⟨Finset.mem_range.2 ht, ht0⟩, Finset.mem_image.2 ⟨l, List.mem_toFinset.2 h, rfl⟩⟩
  rw [← heq, List.mem_toFinset] at hin
  exact hin

theorem sum_getD_le {α : Type} (h : α → Nat) {d : α} (hd : h d = 0) :
    ∀ (L : List α) (n : Nat), ∑ i ∈ Finset.range n, h (L.getD i d) ≤ (L.map h).sum
  | [], n => by simp [hd]
  | x :: xs, 0 => by simp
  | x :: xs, n + 1 => by
    rw [Finset.sum_range_succ', List.getD_cons_zero, List.map_cons, List.sum_cons]
    have := sum_getD_le h hd xs n
    simp only [List.getD_cons_succ]
    omega

theorem sum_blocks (f : Nat → Nat) : ∀ n,
    ∑ t ∈ Finset.range (64 * n), f t = ∑ b ∈ Finset.range n, ∑ i ∈ Finset.range 64, f (64 * b + i)
  | 0 => by simp
  | n + 1 => by
    rw [show 64 * (n + 1) = 64 * n + 64 by ring, Finset.sum_range_add, sum_blocks f n,
      Finset.sum_range_succ (fun b => ∑ i ∈ Finset.range 64, f (64 * b + i)) n]

theorem ties_total : ∑ t ∈ Finset.range 6720, (tiesAt t).1.length ≤ fixTotal := by
  rw [show 6720 = 64 * 105 from rfl, sum_blocks, fixTotal_eq]
  calc ∑ b ∈ Finset.range 105, ∑ i ∈ Finset.range 64, (tiesAt (64 * b + i)).1.length
      = ∑ b ∈ Finset.range 105, ∑ i ∈ Finset.range 64,
          ((TB.getD b []).getD i (([] : List Nat), ([] : List Nat))).1.length := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [tiesAt_eq, show (64 * b + i) / 64 = b by omega, show (64 * b + i) % 64 = i by omega]
    _ ≤ ∑ b ∈ Finset.range 105, blockSum (TB.getD b []) :=
        Finset.sum_le_sum fun b _ => sum_getD_le (fun p : List Nat × List Nat => p.1.length) rfl _ _
    _ ≤ (TB.map blockSum).sum := sum_getD_le blockSum rfl TB 105

theorem fxl_parts : FXL.Pairwise LexLt ∧ (∀ p ∈ FXL, p.1 ∈ (tiesAt p.2).1 ∧ 0 < p.2) ∧
    FXL.length = fixTotal := by
  have h := fxl_ok
  rw [bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, allB_eq,
    allB_eq, List.all_eq_true, List.all_eq_true, Nat.beq_eq, lenK_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨incrP_none _ h1, fun p hp => ⟨(memN_iff _ _).1 (h2 p hp), ?_⟩, h4⟩
  have := h3 p hp
  rwa [Nat.blt_eq] at this

theorem fxl_mem {l t : Nat} (ht0 : 0 < t) (ht : t < 6720) (h : l ∈ (tiesAt t).1) : (l, t) ∈ FXL := by
  obtain ⟨hpw, hmem, hlen⟩ := fxl_parts
  have hnd : FXL.Nodup := hpw.imp fun {p q} hpq => by
    intro e
    subst e
    unfold LexLt at hpq
    omega
  exact complete_of_card (T := fun t => (tiesAt t).1) hnd
    (fun p hp => ⟨(hmem p hp).1, (hmem p hp).2, (bnd_parts.1 p hp).2⟩) hlen ties_total ht0 ht h

@[expose] noncomputable def cnt (L : List (Nat × Nat)) (x : Nat) : Nat := L.countP fun p => p.1 == x

theorem runSum_nil (l f : Nat) :
    runSum [] l f = if f = 0 then (0, 0) else (6720 / (f + 1), 1) := by
  change Bool.rec (motive := fun _ => Nat × Nat) (Nat.div 6720 (Nat.succ f), 1) (0, 0)
    (Nat.beq f 0) = _
  cases f with
  | zero => rfl
  | succ f => rfl

theorem runSum_cons (p : Nat × Nat) (L : List (Nat × Nat)) (l f : Nat) :
    runSum (p :: L) l f = if p.1 = l ∧ 0 < f then runSum L l (f + 1) else
      (if f = 0 then runSum L p.1 1 else ((runSum L p.1 1).1 + 6720 / (f + 1), (runSum L p.1 1).2 + 1)) := by
  change Bool.rec (motive := fun _ => Nat × Nat)
    ((fun r => Bool.rec (motive := fun _ => Nat × Nat)
        (Nat.add r.1 (Nat.div 6720 (Nat.succ f)), Nat.succ r.2) r (Nat.beq f 0)) (runSum L p.1 1))
    (runSum L l (Nat.succ f)) (bAnd(Nat.beq p.1 l, Nat.blt 0 f)) = _
  rw [bAnd_eq]
  by_cases h1 : p.1 = l
  · by_cases h2 : 0 < f
    · have e1 : Nat.beq p.1 l = true := by rw [Nat.beq_eq]; exact h1
      have e2 : Nat.blt 0 f = true := by rw [Nat.blt_eq]; exact h2
      rw [e1, e2, if_pos ⟨h1, h2⟩]
      rfl
    · have e2 : Nat.blt 0 f = false := by
        cases h : Nat.blt 0 f
        · rfl
        · rw [Nat.blt_eq] at h
          exact absurd h h2
      have hf : f = 0 := by omega
      subst hf
      rw [e2, Bool.and_false, if_neg (by omega), if_pos rfl]
      rfl
  · have e1 : Nat.beq p.1 l = false := by
      cases h : Nat.beq p.1 l
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h1
    rw [e1, Bool.false_and, if_neg (by tauto)]
    cases f with
    | zero => rfl
    | succ f => rfl

theorem sum_erase_const {N l : Nat} (hl : l < N) (g : Nat → Nat) (hg : ∀ x ≠ l, g x = 6720) :
    ∑ x ∈ Finset.range N, g x + 6720 = 6720 * N + g l := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hl),
    Finset.sum_congr rfl (fun x hx => hg x (Finset.ne_of_mem_erase hx)), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_range.2 hl), Finset.card_range, smul_eq_mul]
  have : 1 ≤ N := by omega
  calc g l + (N - 1) * 6720 + 6720 = g l + ((N - 1) + 1) * 6720 := by ring
    _ = 6720 * N + g l := by rw [Nat.sub_add_cancel this]; ring

theorem sum_swap_at {N l : Nat} (hl : l < N) {g1 g2 : Nat → Nat} (h : ∀ x ≠ l, g1 x = g2 x) :
    ∑ x ∈ Finset.range N, g1 x + g2 l = ∑ x ∈ Finset.range N, g2 x + g1 l := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hl),
    ← Finset.add_sum_erase _ g2 (Finset.mem_range.2 hl),
    Finset.sum_congr rfl (fun x hx => h x (Finset.ne_of_mem_erase hx))]
  ring

theorem runSum_spec (N : Nat) : ∀ (L : List (Nat × Nat)) (l f : Nat),
    L.Pairwise (fun p q => p.1 ≤ q.1) → (∀ q ∈ L, l ≤ q.1 ∧ q.1 < N) → (0 < f → l < N) →
      (∑ x ∈ Finset.range N, 6720 / (1 + (cnt L x + if x = l then f else 0))) +
          6720 * (runSum L l f).2 = 6720 * N + (runSum L l f).1 ∧
        (runSum L l f).2 ≤ N - l
  | [], l, f, _, _, hf => by
    rw [runSum_nil]
    by_cases h0 : f = 0
    · subst h0
      simp [cnt, Finset.sum_const, Finset.card_range, mul_comm]
    · rw [if_neg h0]
      have hl := hf (Nat.pos_of_ne_zero h0)
      refine ⟨?_, by simp only; omega⟩
      simp only [cnt, List.countP_nil, Nat.zero_add]
      rw [sum_erase_const hl (fun x => 6720 / (1 + if x = l then f else 0))
        (fun x hx => by simp [hx]), if_pos rfl, Nat.add_comm 1 f]
  | p :: L, l, f, hpw, hL, hf => by
    have hpw' := List.pairwise_cons.1 hpw
    have hp := hL p (List.mem_cons_self ..)
    have hcnt : ∀ x, cnt (p :: L) x = cnt L x + if p.1 = x then 1 else 0 := by
      intro x
      unfold cnt
      rw [List.countP_cons]
      by_cases h : p.1 = x <;> simp [h]
    rw [runSum_cons]
    by_cases hc : p.1 = l ∧ 0 < f
    · rw [if_pos hc]
      obtain ⟨ih1, ih2⟩ := runSum_spec N L l (f + 1) hpw'.2
        (fun q hq => hL q (List.mem_cons_of_mem _ hq)) (fun _ => hc.1 ▸ hp.2)
      refine ⟨?_, ih2⟩
      rw [← ih1]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hcnt]
      by_cases hx : x = l
      · subst hx
        rw [if_pos rfl, if_pos hc.1, if_pos rfl]
        congr 1
        omega
      · simp [hx, show p.1 ≠ x by rw [hc.1]; exact Ne.symm hx]
    · rw [if_neg hc]
      obtain ⟨ih1, ih2⟩ := runSum_spec N L p.1 1 hpw'.2
        (fun q hq => ⟨hpw'.1 q hq, (hL q (List.mem_cons_of_mem _ hq)).2⟩) (fun _ => hp.2)
      by_cases h0 : f = 0
      · subst h0
        rw [if_pos rfl]
        refine ⟨?_, by omega⟩
        rw [← ih1]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hcnt]
        by_cases hx : x = p.1
        · subst hx
          simp
        · simp [hx, Ne.symm hx]
      · rw [if_neg h0]
        have hne : p.1 ≠ l := fun e => hc ⟨e, Nat.pos_of_ne_zero h0⟩
        have hlt : l < p.1 := lt_of_le_of_ne hp.1 (Ne.symm hne)
        have hl := hf (Nat.pos_of_ne_zero h0)
        have hcl : cnt L l = 0 := by
          unfold cnt
          rw [List.countP_eq_zero]
          intro q hq
          have := hpw'.1 q hq
          simp only [beq_iff_eq]
          omega
        refine ⟨?_, by simp only; omega⟩
        have e1 := sum_swap_at hl
          (g1 := fun x => 6720 / (1 + (cnt (p :: L) x + if x = l then f else 0)))
          (g2 := fun x => 6720 / (1 + (cnt L x + if x = p.1 then 1 else 0)))
          (fun x hx => by
            rw [hcnt, if_neg hx]
            by_cases hxp : x = p.1
            · subst hxp
              simp
            · simp [hxp, Ne.symm hxp])
        rw [hcl, if_neg hne.symm, if_pos rfl, hcnt, hcl, if_neg hne] at e1
        simp only [Nat.zero_add, Nat.add_zero, Nat.div_one] at e1
        rw [Nat.add_comm 1 f] at e1
        generalize 6720 / (f + 1) = A at e1 ⊢
        generalize ∑ x ∈ Finset.range N, 6720 / (1 + (cnt (p :: L) x + if x = l then f else 0)) =
          S1 at e1 ⊢
        generalize ∑ x ∈ Finset.range N, 6720 / (1 + (cnt L x + if x = p.1 then 1 else 0)) = S2
          at e1 ih1
        generalize (runSum L p.1 1).1 = r1 at ih1 ⊢
        generalize (runSum L p.1 1).2 = r2 at ih1 ih2 ⊢
        clear hcnt hL hpw hpw' hf hc
        rw [Nat.mul_add, Nat.mul_one]
        linarith

theorem sum_lanes : ∑ x ∈ Finset.range NL, 6720 / (1 + cnt FXL x) = 173067389 := by
  have hpw : FXL.Pairwise (fun p q => p.1 ≤ q.1) := fxl_parts.1.imp fun {p q} h => by
    unfold LexLt at h
    omega
  obtain ⟨h1, h2⟩ := runSum_spec NL FXL 0 0 hpw
    (fun q hq => ⟨Nat.zero_le _, (bnd_parts.1 q hq).1⟩) (fun h => absurd h (Nat.lt_irrefl 0))
  have hs : Nat.beq (Nat.add (Nat.mul (Nat.sub NL (runSum FXL 0 0).2) 6720) (runSum FXL 0 0).1)
      173067389 = true := sum_ok
  rw [Nat.beq_eq, nadd, nmul, nsub] at hs
  simp only [ite_self, Nat.add_zero] at h1
  generalize (runSum FXL 0 0).1 = s at h1 hs
  generalize (runSum FXL 0 0).2 = n at h1 h2 hs
  generalize ∑ x ∈ Finset.range NL, 6720 / (1 + cnt FXL x) = S at h1 ⊢
  have hn : n ≤ NL := by omega
  obtain ⟨m, hm⟩ : ∃ m, NL = n + m := ⟨NL - n, by omega⟩
  rw [hm] at h1 hs
  rw [Nat.add_sub_cancel_left] at hs
  rw [Nat.mul_add] at h1
  clear hpw h2 hm hn
  omega

end CertificateChecks.KernelJ4Pent

end
