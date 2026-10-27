module

public import Certificates.Kernel.Sporadic.Fi24ThreeO.FixS
public import Certificates.Kernel.Sporadic.Fi24ThreeO.FixG
public import Certificates.Kernel.Sporadic.Fi24ThreeO.FreeH
public import Certificates.Kernel.Sporadic.Fi24ThreeO.FreeC
public import Certificates.Kernel.Sporadic.Fi24ThreeO.FreeT
public import Certificates.Kernel.Sporadic.Fi24Kit.Facts
public import CFSG.Certificates.Kernel.Spor.Fi24ThreeOSound

public section

namespace CFSG.KD.Fi24ThreeO

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KS.Fi24Net CFSG.KS.Fi24NetPt CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO CFSG.KD.Fi24Net
  CFSG.KD.Fi24Kit CFSG.KC.Benes Finset

theorem blt_t {a b : Nat} (h : Nat.blt a b = true) : a < b := by rwa [Nat.blt_eq] at h

theorem blt_of {a b : Nat} (h : a < b) : Nat.blt a b = true := by rwa [Nat.blt_eq]

theorem NW_ge {j : Nat} (hj : 13 ≤ j) (l : Nat) : NW j l = 0 := by
  have b : ∀ a c : Nat, c ≤ a → Nat.blt a c = false := fun a c h => by
    cases e : Nat.blt a c
    · rfl
    · exact absurd (blt_t e) (by omega)
  have q : ∀ a c : Nat, a ≠ c → Nat.beq a c = false := fun a c h => beq_false h
  unfold NW
  rw [b j 7 (by omega), q j 7 (by omega), q j 8 (by omega), q j 9 (by omega), q j 10 (by omega),
    q j 11 (by omega), q j 12 (by omega)]

theorem vn : VN NW NT := by
  refine ⟨tP_facts.1, fun j => ?_⟩
  by_cases hj : j < 13
  · exact NW_nv hj
  · intro l _ p hp
    rw [NW_ge (by omega) l, Nat.zero_testBit] at hp
    exact absurd hp (by decide)

theorem CF_pts {c x : Nat} (hc : c ≤ 26) (hx : x < 306936) : CF NW NT c x < 306936 := by
  unfold CF
  by_cases h : c = 26
  · rw [if_pos h]
    exact tP_facts.2.2.1 x hx
  · rw [if_neg h]
    unfold LN
    split_ifs
    · exact (nets (by omega) hx).1
    · exact (nets (by omega) hx).2.1

theorem cP_pts : ∀ {cs : List Nat}, (∀ c ∈ cs, c ≤ 26) → ∀ {x : Nat}, x < 306936 →
    cP NW NT cs x < 306936
  | [], _, _, hx => hx
  | c :: cs, h, _, hx =>
    CF_pts (h c List.mem_cons_self) (cP_pts (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) hx)

theorem invC_cons (c : Nat) (W : List Nat) :
    invC (c :: W) = invC W ++ [nIf(Nat.beq c (nat_lit 26), nat_lit 26, Nat.xor c (nat_lit 1))] := rfl

theorem CF_inv {c : Nat} (hc : c < 26) (x : Nat) :
    CF NW NT (nIf(Nat.beq c (nat_lit 26), nat_lit 26, Nat.xor c (nat_lit 1))) (CF NW NT c x) = x := by
  rw [beq26' (by omega)]
  change CF NW NT (c ^^^ 1) (CF NW NT c x) = x
  have hRF : ∀ j y, pR (NW j) (pF (NW j) y) = y := fun j y => pR_pF (vn.2 j) y
  have hFR : ∀ j y, pF (NW j) (pR (NW j) y) = y := fun j y => pF_pR (vn.2 j) y
  interval_cases c <;> simp [CF, LN, hRF, hFR]

theorem invC_lt : ∀ {W : List Nat}, (∀ c ∈ W, c < 26) → ∀ c ∈ invC W, c < 26
  | [], _, _, h => absurd h List.not_mem_nil
  | c :: W, h, d, hd => by
    rw [invC_cons, List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact invC_lt (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) d hd
    · have hc := h c List.mem_cons_self
      rw [beq26' (by omega)]
      change c ^^^ 1 < 26
      interval_cases c <;> decide

theorem cP_invC : ∀ {W : List Nat}, (∀ c ∈ W, c < 26) → ∀ x, cP NW NT (invC W) (cP NW NT W x) = x
  | [], _, _ => rfl
  | c :: W, h, x => by
    rw [invC_cons, cP_append, cP_cons, cP_cons]
    change cP NW NT (invC W) (CF NW NT _ (CF NW NT c (cP NW NT W x))) = x
    rw [CF_inv (h c List.mem_cons_self)]
    exact cP_invC (fun c' hc' => h c' (List.mem_cons_of_mem c hc')) x

@[expose] def TF (W : List Nat) (k : Nat) : Prop :=
  cP NW NT (invC W) k < 306936 ∧ pF NT (cP NW NT (invC W) k) = cP NW NT (invC W) k

theorem fixT_iff (y : Nat) : (fixC NW NT [26]).testBit y = true ↔ y < 306936 ∧ pF NT y = y := by
  rw [testBit_fixC vn]
  rfl

structure FixN (r : Nat) : Prop where
  cube : ∀ x < 306936, cP NW NT (wr r ++ (wr r ++ wr r)) x = x
  base : cP NW NT (wr r) 0 = 0 ∧ cP NW NT (wr r) 305530 = 305530 ∧ cP NW NT (wr r) 5604 = 5604 ∧
    cP NW NT (wr r) (yr r) = yr r
  moves : cP NW NT (wr r) 1 ≠ 1
  tests : ∀ W ∈ tw r, cP NW NT W 0 < 306936 ∧ cP NW NT (wr r) (cP NW NT W 0) = cP NW NT W 0
  sep : ∀ k k', k < 306936 → k' < 306936 → cP NW NT (wr r) k = k → cP NW NT (wr r) k' = k' → k ≠ k' →
    (∃ W ∈ tw r, (TF W k ∧ ¬ TF W k') ∨ (¬ TF W k ∧ TF W k')) ∨
      clsK OL NT k k' ≠ k' ∨ clsK OL NT k' k ≠ k
  p1 : ∀ k < 306936, cP NW NT (wr r) k = k → ∃ W ∈ tw r, ¬ TF W k
  pairs : ∀ p ∈ gp r, cP NW NT p.1 0 < 306936 ∧ cP NW NT (wr r) (cP NW NT p.1 0) = cP NW NT p.1 0 ∧
    cP NW NT p.2 0 < 306936 ∧ cP NW NT (wr r) (cP NW NT p.2 0) = cP NW NT p.2 0
  gens : ∀ k < 306936, cP NW NT (wr r) k ≠ k →
    (∃ p ∈ gp r, cP NW NT (dW p.1 ++ dW p.2) k ≠ k ∧
        cP NW NT (dW p.1 ++ dW p.2) k ≠ cP NW NT (wr r) k ∧
        cP NW NT (dW p.1 ++ dW p.2) k ≠ cP NW NT (wr r ++ wr r) k) ∨
      clsK OL NT k (cP NW NT (wr r) k) ≠ cP NW NT (wr r) k ∨
      ∃ d e, d < 306936 ∧ e < 306936 ∧ cP NW NT (wr r) d = d ∧ cP NW NT (wr r) e = e ∧
        clsK OL NT d (clsK OL NT e k) ≠ k ∧ clsK OL NT d (clsK OL NT e k) ≠ cP NW NT (wr r) k ∧
        clsK OL NT d (clsK OL NT e k) ≠ cP NW NT (wr r ++ wr r) k

theorem TF_bit (W : List Nat) (k : Nat) :
    (fixC NW NT [26]).testBit (cP NW NT (invC W) k) = true ↔ TF W k :=
  fixT_iff _

theorem fixN_of {r : Nat} (h1 : fx r = true) (h2 : cu r = true) (h3 : sp r = true) (h4 : gn r = true) :
    FixN r := by
  have hF : ∀ x, (fixC NW NT (wr r)).testBit x = true ↔ x < 306936 ∧ cP NW NT (wr r) x = x :=
    testBit_fixC vn (wr r)
  obtain ⟨s1, s2, s3⟩ := sepOK_spec vn h3
  obtain ⟨g1, g2⟩ := gensOK_spec vn h4
  unfold fx at h1
  obtain ⟨f1, f2⟩ := CFSG.KC.Benes.andB_true h1
  have fb' : ∀ b ∈ [0, 305530, 5604, yr r], cP NW NT (wr r) b = b := fun b hb => by
    rw [← ptC_eq]
    exact Nat.eq_of_beq_eq_true (CFSG.KS.Fi24ThreeO.allL_spec f1 b hb)
  refine ⟨cubeOK_spec vn h2, ⟨fb' 0 (by simp), fb' 305530 (by simp), fb' 5604 (by simp),
    fb' (yr r) (by simp)⟩, fun e => ?_, fun W hW => (hF _).1 (s1 W hW), ?_, ?_, ?_, ?_⟩
  · rw [ptC_eq, e, Nat.beq_refl] at f2
    exact absurd f2 (by decide)
  · intro k k' hk hk' fk fk' hne
    rcases s2 k k' ((hF k).2 ⟨hk, fk⟩) ((hF k').2 ⟨hk', fk'⟩) hne with ⟨W, hW, hd⟩ | h | h
    · refine Or.inl ⟨W, hW, ?_⟩
      rw [← TF_bit, ← TF_bit]
      revert hd
      cases (fixC NW NT [26]).testBit (cP NW NT (invC W) k) <;>
        cases (fixC NW NT [26]).testBit (cP NW NT (invC W) k') <;> simp
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro k hk fk
    obtain ⟨W, hW, hb⟩ := s3 k ((hF k).2 ⟨hk, fk⟩)
    refine ⟨W, hW, fun ht => ?_⟩
    rw [← TF_bit, hb] at ht
    exact absurd ht (by decide)
  · intro p hp
    obtain ⟨a, b⟩ := g1 p hp
    exact ⟨((hF _).1 a).1, ((hF _).1 a).2, ((hF _).1 b).1, ((hF _).1 b).2⟩
  · intro k hk hm
    rcases g2 k hk hm with h | h | ⟨d, e, hd, he, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨d, e, ((hF d).1 hd).1, ((hF e).1 he).1, ((hF d).1 hd).2,
        ((hF e).1 he).2, h⟩)

theorem fix_facts : ∀ r < 4, FixN r := by
  intro r hr
  interval_cases r
  exacts [fixN_of Ck.fx0 Ck.cu0 Ck.sp0 Ck.gn0, fixN_of Ck.fx1 Ck.cu1 Ck.sp1 Ck.gn1,
    fixN_of Ck.fx2 Ck.cu2 Ck.sp2 Ck.gn2, fixN_of Ck.fx3 Ck.cu3 Ck.sp3 Ck.gn3]

theorem letters_lt : (∀ r < 4, ∀ c ∈ wr r, c < 26) ∧
    (∀ r < 4, ∀ W ∈ tw r, ∀ c ∈ W, c < 26) ∧ (∀ r < 4, ∀ p ∈ gp r, (∀ c ∈ p.1, c < 26) ∧ ∀ c ∈ p.2, c < 26) := by
  decide +kernel

theorem lv_facts : ∃ P : Nat, P.testBit 14069 = true ∧
    (∀ x, P.testBit x = true → ∃ v : List Nat, (∀ l ∈ v, l ∈ lv3) ∧ wN NW v x = 14069) ∧
    (∀ x < 524288, ∀ l ∈ lv3, P.testBit (LN NW l x) = true → P.testBit x = true) ∧
    #((range 524288).filter (fun x => P.testBit x = true)) = 1152 :=
  orbOK_spec vn Ck.lv_t

@[expose] def InQN (x : Nat) : Prop := clsK OL NT x (LN NW 2 x) = LN NW 2 x

structure FreeN : Prop where
  cube : ∀ x < 306936, cP NW NT [2, 2, 2] x = x
  fpf : ∀ x < 306936, cP NW NT [2] x ≠ x
  hcomm : ∀ j < 6, ∀ b ∈ base, cP NW NT (invC G1 ++ (nthD [] eps j ++ (G1 ++ [2]))) b =
    cP NW NT (2 :: (invC G1 ++ (nthD [] eps j ++ G1))) b
  hcov : ∀ x < 306936, ∃ v, InW hw v ∧ cP NW NT (invC G1 ++ (v ++ G1)) x ∈ hr
  hq : ∀ i < 12, (i < 3 → PQ.testBit (nthD 0 hr i) = true ∧ InQN (nthD 0 hr i)) ∧
    (3 ≤ i → PQ.testBit (nthD 0 hr i) = false ∧ ¬ InQN (nthD 0 hr i))
  hr_len : hr.length = 12
  lks : nthD 0 hr 0 = 12 ∧ ∀ i < 2, PQ.testBit (nthD 0 lk i) = true ∧
    uP NW OL NT (nthD 0 lk i) 12 = nthD 0 hr (i + 1)
  pq_pts : ∀ x, PQ.testBit x = true → x < 306936
  qcl : ∀ x < 306936, ∀ w ∈ hw, PQ.testBit (cP NW NT (invC G1 ++ (w ++ G1)) x) = true →
    PQ.testBit x = true
  cst : ∀ w ∈ swC, cP NW NT (invC G1 ++ (w ++ G1)) 12 = 12 ∨
    cP NW NT (invC G1 ++ (w ++ G1)) 12 = LN NW 2 12 ∨
    cP NW NT (invC G1 ++ (w ++ G1)) 12 = LN NW 2 (LN NW 2 12)
  ccov : ∀ x < 306936, PQ.testBit x = true → x ≠ 12 → x ≠ LN NW 2 12 → x ≠ LN NW 2 (LN NW 2 12) →
    ∃ v, InW swC v ∧ (cP NW NT (invC G1 ++ (v ++ G1)) x ∈ crx ∨
      cF.testBit (cP NW NT (invC G1 ++ (v ++ G1)) x) = true)
  ct : ∀ c ∈ cr, (c.2.2.2 = 306936 → c.2.2.1 % 3 = 0 ∧ c.2.2.1 ≠ 0 ∧
      (fun q => uP NW OL NT 12 (uP NW OL NT c.1 q))^[c.2.2.1] c.2.1 = c.2.1 ∧
      (fun q => uP NW OL NT 12 (uP NW OL NT c.1 q))^[c.2.2.1 / 3] c.2.1 ≠ c.2.1) ∧
    (c.2.2.2 ≠ 306936 → PQ.testBit c.2.2.2 = true ∧ c.2.2.1 % 3 = 0 ∧ c.2.2.1 ≠ 0 ∧
      (fun q => uP NW OL NT 12 (uP NW OL NT c.1 (uP NW OL NT c.2.2.2
        (uP NW OL NT 12 (uP NW OL NT c.1 (uP NW OL NT c.2.2.2 q))))))^[c.2.2.1] c.2.1 = c.2.1 ∧
      (fun q => uP NW OL NT 12 (uP NW OL NT c.1 (uP NW OL NT c.2.2.2
        (uP NW OL NT 12 (uP NW OL NT c.1 (uP NW OL NT c.2.2.2 q))))))^[c.2.2.1 / 3] c.2.1 ≠ c.2.1)
  bg : PQ.testBit (cP NW NT bk 0) = true ∧ PQ.testBit (cP NW NT bl 0) = true ∧
    ∀ x < 306936, PQ.testBit x = true →
      cP NW NT (uC bk ++ uC bl) x ≠ x ∧ cP NW NT (uC bk ++ uC bl) x ≠ cP NW NT [2] x ∧
        cP NW NT (uC bk ++ uC bl) x ≠ cP NW NT [2, 2] x
  bs : ∀ i < 6, PQ.testBit (nthD (0, 0) fb i).1 = true ∧ PQ.testBit (nthD (0, 0) fb i).2 = true ∧
    clsK OL NT (nthD (0, 0) fb i).1 (nthD (0, 0) fb i).2 = nthD 0 base i

theorem bitN_one (n i : Nat) : Nat.beq (bitN n i) 1 = n.testBit i := by
  unfold bitN
  rw [nland, nshr, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h | h <;> rw [h] <;> rfl

theorem bit_of {n i : Nat} (h : Nat.beq (bitN n i) 1 = true) : n.testBit i = true := by
  rw [← bitN_one]
  exact h

theorem nthD_eq {α : Type} (d : α) : ∀ (l : List α) (i : Nat) (hi : i < l.length), nthD d l i = l[i]
  | [], _, hi => absurd hi (by simp)
  | a :: l, 0, _ => rfl
  | a :: l, i + 1, hi => nthD_eq d l i (by simpa using hi)

theorem nthD_mem {α : Type} (d : α) {l : List α} {i : Nat} (hi : i < l.length) : nthD d l i ∈ l := by
  rw [nthD_eq d l i hi]
  exact List.getElem_mem hi

theorem G1_lt : ∀ c ∈ G1, c < 26 := by decide

theorem G1_le : ∀ c ∈ G1, c ≤ 26 := fun c h => by have := G1_lt c h; omega

theorem gfr_bit (S : Nat) {y : Nat} (hy : y < 524288) :
    (gfr S).testBit y = S.testBit (cP NW NT (invC G1) y) := testBit_wkC vn _ S hy

theorem cP_G1_lt {x : Nat} (hx : x < 306936) : cP NW NT G1 x < 524288 := by
  have := cP_pts G1_le hx
  omega

theorem cP_conj (v : List Nat) (x : Nat) :
    cP NW NT (invC G1 ++ (v ++ G1)) x = cP NW NT (invC G1) (cP NW NT v (cP NW NT G1 x)) := by
  rw [cP_append, cP_append]

theorem sP_eq (x : Nat) : sP x = LN NW 2 x := letN_eq _ _ _

theorem inQ_iff (x : Nat) : inQ x = true ↔ InQN x := by
  unfold inQ InQN
  rw [sP_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h, Nat.beq_refl]⟩

theorem andB_t {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := CFSG.KC.Benes.andB_true h

theorem cF_bit {z : Nat} (h : cF.testBit z = true) :
    ¬ z < 306936 ∨ PQ.testBit z = false ∨ z = 12 ∨ z = LN NW 2 12 ∨ z = LN NW 2 (LN NW 2 12) := by
  unfold cF at h
  rw [nlor, Nat.testBit_or, Bool.or_eq_true, nxor, Nat.testBit_xor, nland, Nat.testBit_and,
    testBit_plOf, sP_eq, sP_eq] at h
  by_cases hz : z < 306936
  · rw [ptsM_bit hz, Bool.and_true] at h
    rcases h with h | h
    · right
      left
      cases e : PQ.testBit z
      · rfl
      · rw [e] at h
        exact absurd h (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr (Or.inr h)
  · exact Or.inl hz

theorem free_facts : FreeN := by
  have hr_len : hr.length = 12 := by decide
  refine ⟨fun x hx => cubeOK_spec vn Ck.cuF_t x hx, fun x hx e => ?_, ?_, ?_, ?_, hr_len, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h0 : fixC NW NT [2] = 0 := Nat.eq_of_beq_eq_true Ck.fpf_t
    have hb : (fixC NW NT [2]).testBit x = true := (testBit_fixC vn [2] x).2 ⟨hx, e⟩
    rw [h0, Nat.zero_testBit] at hb
    exact absurd hb (by decide)
  ·
    intro j hj b hb
    have hc : hc j = true := by
      interval_cases j
      exacts [Ck.hc0, Ck.hc1, Ck.hc2, Ck.hc3, Ck.hc4, Ck.hc5]
    have := Nat.eq_of_beq_eq_true (allL_spec hc b hb)
    rw [ptC_eq, ptC_eq] at this
    exact this
  ·
    intro x hx
    rcases covW_spec vn Ck.hcov_t (x := cP NW NT G1 x) (cP_pts G1_le hx) with h | ⟨v, hv, hS⟩
    · rw [Nat.zero_testBit] at h
      exact absurd h (by decide)
    · refine ⟨v, hv, ?_⟩
      rw [gfr_bit _ (cP_lt vn v (cP_G1_lt hx)), testBit_plOf] at hS
      rw [cP_conj]
      exact hS
  ·
    intro i hi
    have key := allI_spec Ck.hq_t i (by rw [hr_len]; exact hi)
    rw [Nat.zero_add, letB_eq', ← nthD_eq 0 hr i (by rw [hr_len]; exact hi)] at key
    obtain ⟨k1, k2⟩ := andB_t key
    refine ⟨fun h3 => ?_, fun h3 => ?_⟩
    · have hb : Nat.blt i 3 = true := blt_of h3
      rw [hb] at k1 k2
      change Nat.beq (bitN PQ (nthD 0 hr i)) 1 = true at k1
      change inQ (nthD 0 hr i) = true at k2
      exact ⟨bit_of k1, (inQ_iff _).1 k2⟩
    · have hb : Nat.blt i 3 = false := by
        cases e : Nat.blt i 3
        · rfl
        · exact absurd (blt_t e) (by omega)
      rw [hb] at k1 k2
      change Nat.beq (bitN PQ (nthD 0 hr i)) 0 = true at k1
      change notB (inQ (nthD 0 hr i)) = true at k2
      refine ⟨?_, fun hq => ?_⟩
      · have e := Nat.eq_of_beq_eq_true k1
        cases e' : PQ.testBit (nthD 0 hr i)
        · rfl
        · rw [← bitN_one, e] at e'
          exact absurd e' (by decide)
      · rw [(inQ_iff _).2 hq] at k2
        exact absurd k2 (by decide)
  ·
    obtain ⟨l1, l2⟩ := andB_t Ck.lks_t
    obtain ⟨l3, l4⟩ := andB_t l2
    have hlk : lk.length = 2 := by decide
    refine ⟨Nat.eq_of_beq_eq_true l4, fun i hi => ?_⟩
    have key := allI_spec l1 i (by rw [hlk]; exact hi)
    rw [Nat.zero_add, ← nthD_eq 0 lk i (by rw [hlk]; exact hi)] at key
    obtain ⟨k1, k2⟩ := andB_t key
    exact ⟨bit_of k1, Nat.eq_of_beq_eq_true k2⟩
  ·
    intro x hx
    obtain ⟨q1, -⟩ := andB_t Ck.qcl_t
    have e : (PQ &&& ptsM).testBit x = PQ.testBit x := by rw [← nland, Nat.eq_of_beq_eq_true q1]
    rw [Nat.testBit_and, hx, Bool.true_and] at e
    by_contra hc
    rw [ptsM_bit' hc] at e
    exact absurd e (by decide)
  ·
    intro x hx w hw hP
    obtain ⟨-, q2⟩ := andB_t Ck.qcl_t
    have hy := cP_G1_lt hx
    have h1 : (gfr PQ).testBit (cP NW NT w (cP NW NT G1 x)) = true := by
      rw [gfr_bit _ (cP_lt vn w hy), ← cP_conj]
      exact hP
    have h2 := closW_spec vn q2 hy hw h1
    rw [gfr_bit _ hy, cP_invC G1_lt] at h2
    exact h2
  ·
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hw
    have hl : swC.length = 3 := by decide
    have hc : cst j = true := by
      rw [hl] at hj
      interval_cases j
      exacts [Ck.cst0, Ck.cst1, Ck.cst2]
    unfold cst at hc
    rw [letB_eq', nthD_eq [] swC j hj, ptC_eq, sP_eq, sP_eq] at hc
    change orB _ (orB _ _) = true at hc
    simp only [CFSG.KC.orB, Bool.rec] at hc
    revert hc
    cases e1 : Nat.beq (cP NW NT (invC G1 ++ (swC[j] ++ G1)) 12) 12 <;>
      cases e2 : Nat.beq (cP NW NT (invC G1 ++ (swC[j] ++ G1)) 12) (LN NW 2 12) <;>
      cases e3 : Nat.beq (cP NW NT (invC G1 ++ (swC[j] ++ G1)) 12) (LN NW 2 (LN NW 2 12)) <;>
      intro hc <;> first
        | exact absurd hc (by decide)
        | exact Or.inl (Nat.eq_of_beq_eq_true e1)
        | exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true e2))
        | exact Or.inr (Or.inr (Nat.eq_of_beq_eq_true e3))
  ·
    intro x hx hq h0 h1 h2
    have hy := cP_G1_lt hx
    rcases covW_spec vn Ck.ccov_t (x := cP NW NT G1 x) (cP_pts G1_le hx) with h | ⟨v, hv, hS⟩
    · rw [gfr_bit _ hy, cP_invC G1_lt] at h
      rcases cF_bit h with h' | h' | h' | h' | h'
      · exact absurd hx h'
      · rw [hq] at h'
        exact absurd h' (by decide)
      · exact absurd h' h0
      · exact absurd h' h1
      · exact absurd h' h2
    · refine ⟨v, hv, ?_⟩
      rw [gfr_bit _ (cP_lt vn v hy), ← cP_conj, nlor, Nat.testBit_or, Bool.or_eq_true,
        testBit_plOf] at hS
      exact hS
  ·
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hc
    have hl : cr.length = 26 := by decide
    have hct : ct i = true := by
      rw [hl] at hi
      interval_cases i
      exacts [Ck.ct0, Ck.ct1, Ck.ct2, Ck.ct3, Ck.ct4, Ck.ct5, Ck.ct6, Ck.ct7, Ck.ct8, Ck.ct9,
        Ck.ct10, Ck.ct11, Ck.ct12, Ck.ct13, Ck.ct14, Ck.ct15, Ck.ct16, Ck.ct17, Ck.ct18, Ck.ct19,
        Ck.ct20, Ck.ct21, Ck.ct22, Ck.ct23, Ck.ct24, Ck.ct25]
    unfold ct at hct
    rw [nthD_eq _ cr i hi] at hct
    beta_reduce at hct
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have hb : Nat.beq cr[i].2.2.2 306936 = true := by rw [e]; rfl
      rw [hb] at hct
      exact cycK_spec hct
    · have hb : Nat.beq cr[i].2.2.2 306936 = false := beq_false e
      rw [hb] at hct
      obtain ⟨c1, c2⟩ := andB_t hct
      exact ⟨bit_of c1, cycK_spec c2⟩
  ·
    obtain ⟨b1, b2⟩ := andB_t Ck.bg_t
    obtain ⟨b2, b3⟩ := andB_t b2
    refine ⟨?_, ?_, fun x hx hP => offOK_spec vn b3 x hx hP⟩
    · rw [← ptC_eq]
      exact bit_of b1
    · rw [← ptC_eq]
      exact bit_of b2
  ·
    intro i hi
    have hc : bs i = true := by
      interval_cases i
      exacts [Ck.bs0, Ck.bs1, Ck.bs2, Ck.bs3, Ck.bs4, Ck.bs5]
    unfold bs at hc
    obtain ⟨c1, c2⟩ := andB_t hc
    obtain ⟨c3, c4⟩ := andB_t c1
    exact ⟨bit_of c3, bit_of c4, Nat.eq_of_beq_eq_true c2⟩

end CFSG.KD.Fi24ThreeO

end
