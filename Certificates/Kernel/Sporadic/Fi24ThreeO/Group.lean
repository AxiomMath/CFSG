
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeFree

public section

namespace CFSG.KD.Fi24ThreeO.Group

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Th CFSG.KC CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KS.Fi24Net CFSG.KS.Fi24Kit CFSG.KS.Fi24ThreeO CFSG.KD.Fi24Net CFSG.KD.Fi24Kit CFSG.KD.Fi24ThreeO
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (three_dvd_orderOf_of_smul_cycle)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

structure Bridge : Prop where
  letter : ∀ l < 26, ∀ x : Fin 306936, ((pairG gs l) • x).val = LN NW l x.val
  cls : ∀ k p : Fin 306936, (cls k • p).val = clsK OL NT k.val p.val

theorem wordElt_nil : wordElt [] = 1 := rfl

theorem wordElt_cons (l : ℕ) (w : List ℕ) : wordElt (l :: w) = pairG gs l * wordElt w := by
  unfold wordElt
  rw [List.map_cons, List.prod_cons]

theorem wordElt_append (u v : List ℕ) : wordElt (u ++ v) = wordElt u * wordElt v := by
  unfold wordElt
  rw [List.map_append, List.prod_append]

theorem word_val (hB : Bridge) : ∀ (w : List ℕ), (∀ l ∈ w, l < 26) → ∀ x : Fin 306936,
    ((wordElt w) • x).val = cP NW NT w x.val
  | [], _, x => by rw [wordElt_nil, one_smul]; rfl
  | l :: w, hw, x => by
    rw [wordElt_cons, mul_smul, hB.letter l (hw l List.mem_cons_self), word_val hB w
      (fun l' h => hw l' (List.mem_cons_of_mem l h)) x, cP_cons]
    unfold CF
    rw [if_neg (by have := hw l List.mem_cons_self; omega)]

theorem word_inv_val (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) (x : Fin 306936) :
    ((wordElt w)⁻¹ • x).val = cP NW NT (invC w) x.val := by
  have e := word_val hB w hw ((wordElt w)⁻¹ • x)
  rw [smul_inv_smul] at e
  rw [e, cP_invC hw]

theorem eq_of_val {g h : J} (e : ∀ x : Fin 306936, (g • x).val = (h • x).val) : g = h := by
  have : g⁻¹ * h = 1 := eq_one_of_idx fun i hi => by
    rw [idx_of_lt _ hi, mul_smul]
    have e' : h • (⟨i, hi⟩ : Fin 306936) = g • ⟨i, hi⟩ := (Fin.ext (e _)).symm
    rw [e', inv_smul_smul]
  rw [← mul_inv_cancel_left g h, this, mul_one]

theorem wordElt_invC (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) :
    wordElt (invC w) = (wordElt w)⁻¹ :=
  eq_of_val fun x => by rw [word_val hB _ (invC_lt hw), word_inv_val hB hw]

theorem clsK_zero (p : ℕ) : clsK OL NT 0 p = pF NT p := by
  unfold clsK
  rw [CFSG.KS.Fi24NetPt.strictN_eq, CFSG.KS.Fi24NetPt.strictN_eq, ← CFSG.KS.Fi24NetPt.ptF_eq]
  rfl

theorem cls_root : cls CFSG.Sporadic.Fi24.root = tR := by
  have h := CFSG.Sporadic.Fi24.cls_smul_root (1 : J)
  rw [one_smul, map_one, one_mul, inv_one, mul_one] at h
  exact h

theorem tR_val (hB : Bridge) (p : Fin 306936) : (tR • p).val = pF NT p.val := by
  rw [← cls_root, hB.cls]
  exact clsK_zero _

theorem cls_word (hB : Bridge) {W : List ℕ} (hW : ∀ l ∈ W, l < 26) (k : Fin 306936) :
    (cls (wordElt W • CFSG.Sporadic.Fi24.root) • k).val = cP NW NT (dW W) k.val := by
  rw [CFSG.Sporadic.Fi24.cls_smul_root, mul_smul, mul_smul, ← map_inv,
    CFSG.Sporadic.Fi24.jR_smul, CFSG.Sporadic.Fi24.jR_smul, word_val hB W hW, tR_val hB,
    word_inv_val hB hW]
  unfold dW
  rw [cP_append, cP_cons]
  unfold CF
  rw [if_pos rfl]

theorem root_val (W : List ℕ) (hB : Bridge) (hW : ∀ l ∈ W, l < 26) :
    (wordElt W • CFSG.Sporadic.Fi24.root).val = cP NW NT W 0 := word_val hB W hW _

theorem TF_iff (hB : Bridge) {W : List ℕ} (hW : ∀ l ∈ W, l < 26) (k : Fin 306936) :
    TF W k.val ↔ cls (wordElt W • CFSG.Sporadic.Fi24.root) • k = k := by
  rw [CFSG.Sporadic.Fi24.cls_smul_root, mul_smul, mul_smul, ← map_inv,
    CFSG.Sporadic.Fi24.jR_smul, CFSG.Sporadic.Fi24.jR_smul, smul_eq_iff_eq_inv_smul, eq_comm,
    ← Fin.val_eq_val, tR_val hB, word_inv_val hB hW]
  unfold TF
  have hl : cP NW NT (invC W) k.val < 306936 := by
    rw [← word_inv_val hB hW]
    exact Fin.isLt _
  exact ⟨fun h => h.2.symm, fun h => ⟨hl, h.symm⟩⟩

theorem comm_iff (t k : Fin 306936) : cls t * cls k = cls k * cls t ↔ cls t • k = k :=
  (CFSG.Sporadic.FischerOddCore.cls_smul_eq_iff t k).symm

theorem cls_val (hB : Bridge) (k p : ℕ) (hk : k < 306936) (hp : p < 306936) :
    (cls (⟨k, hk⟩ : Fin 306936) • (⟨p, hp⟩ : Fin 306936)).val = clsK OL NT k p := hB.cls _ _

theorem chainBase_eq : CFSG.Sporadic.Fi24.Native.chainBase =
    #[0, 305530, 5604, 221549, 266275, 186844] := by decide

theorem cb_lt (t : ℕ) (ht : t < 6) : CFSG.Sporadic.Fi24.Native.chainBase[t]! < 306936 :=
  CFSG.Sporadic.Fi24.chainBase_lt t ht

theorem eq_of_base {g h : J}
    (hb : ∀ (t : ℕ) (ht : t < 6), g • (⟨CFSG.Sporadic.Fi24.Native.chainBase[t]!, cb_lt t ht⟩ :
      Fin 306936) = h • ⟨CFSG.Sporadic.Fi24.Native.chainBase[t]!, cb_lt t ht⟩) :
    g = h := by
  have hmem : g⁻¹ * h ∈ lvl 6 := mem_lvl_of_fix (le_refl 6) fun t ht => by
    rw [idx_of_lt _ (cb_lt t ht), mul_smul, ← hb t ht, inv_smul_smul]
  have hcard : Nat.card (lvl 6) = 1 := by
    rw [CFSG.Sporadic.Fi24.chain_facts'.2.2 6 (by rw [CFSG.Sporadic.Fi24.chainBase_size]),
      CFSG.Sporadic.Fi24.chainBase_size, Finset.Ico_self, Finset.prod_empty]
  have hbot := Subgroup.eq_bot_of_card_eq (lvl 6) hcard
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [← mul_inv_cancel_left g h, hmem, mul_one]

theorem comm_inv' {n s : J} (h : n * s = s * n) : n⁻¹ * s = s * n⁻¹ := by
  calc n⁻¹ * s = n⁻¹ * (s * n) * n⁻¹ := by group
    _ = n⁻¹ * (n * s) * n⁻¹ := by rw [h]
    _ = s * n⁻¹ := by group

theorem comm_pow' {n s : J} (h : n * s = s * n) : ∀ k : ℕ, n * s ^ k = s ^ k * n
  | 0 => by rw [pow_zero, mul_one, one_mul]
  | k + 1 => by rw [pow_succ, ← mul_assoc, comm_pow' h k, mul_assoc, h, ← mul_assoc]

theorem letters_size26 : letters.size = 26 := by
  rw [CFSG.Sporadic.Fi24.letters_size, CFSG.Sporadic.Fi24.chainWords_size]

theorem pow3_of (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26)
    (h : ∀ x < 306936, cP NW NT (w ++ (w ++ w)) x = x) : wordElt w ^ 3 = 1 := by
  have hw3 : ∀ l ∈ w ++ (w ++ w), l < 26 := by
    intro l hl
    simp only [List.mem_append] at hl
    rcases hl with hl | hl | hl <;> exact hw l hl
  have e : wordElt w ^ 3 = wordElt (w ++ (w ++ w)) := by
    rw [wordElt_append, wordElt_append, pow_three]
  rw [e]
  apply eq_one_of_idx
  intro i hi
  rw [idx_of_lt _ hi, word_val hB _ hw3]
  exact h i hi

theorem fixFacts_of (hB : Bridge) {r : ℕ} (hr : r < 4) : FixFacts (wr r) (yr r) := by
  have hF := fix_facts r hr
  obtain ⟨hwl, htl, hpl⟩ := letters_lt
  have hw := hwl r hr
  have sv : ∀ x : Fin 306936, ((wordElt (wr r)) • x).val = cP NW NT (wr r) x.val :=
    word_val hB _ hw
  have hy : yr r < 306936 := by interval_cases r <;> decide
  have fixv : ∀ x : Fin 306936, wordElt (wr r) • x = x ↔ cP NW NT (wr r) x.val = x.val := by
    intro x
    rw [← Fin.val_eq_val, sv]
  refine ⟨fun l hl => by rw [letters_size26]; exact hw l hl, pow3_of hB hw hF.cube, ?_, ?_, hy, ?_,
    ?_, ?_, ?_⟩
  ·
    intro h1
    have := sv ⟨1, by norm_num⟩
    rw [h1, one_smul] at this
    exact hF.moves this.symm
  ·
    intro t ht
    rw [idx_of_lt _ (cb_lt t (by omega)), sv]
    obtain ⟨b0, b1, b2, -⟩ := hF.base
    interval_cases t
    · exact b0
    · exact b1
    · exact b2
  · rw [idx_of_lt _ hy, sv]
    exact hF.base.2.2.2
  ·
    intro k k' hk hk' hne hc
    rcases hF.sep k k' k.2 k'.2 ((fixv k).1 hk) ((fixv k').1 hk') (fun e => hne (Fin.ext e)) with
      ⟨W, hW, hd⟩ | h | h
    · have hWl := htl r hr W hW
      obtain ⟨tl, tf⟩ := hF.tests W hW
      refine ⟨wordElt W • CFSG.Sporadic.Fi24.root, ?_, ?_⟩
      · rw [fixv, root_val W hB hWl]
        exact tf
      · rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨(comm_iff _ _).2 ((TF_iff hB hWl k).1 h1),
            fun e => h2 ((TF_iff hB hWl k').2 ((comm_iff _ _).1 e))⟩
        · exact Or.inr ⟨fun e => h1 ((TF_iff hB hWl k).2 ((comm_iff _ _).1 e)),
            (comm_iff _ _).2 ((TF_iff hB hWl k').1 h2)⟩
    · exfalso
      apply h
      have e := (comm_iff k k').1 (hc)
      rw [← hB.cls, e]
    · exfalso
      apply h
      have e := (comm_iff k' k).1 hc.symm
      rw [← hB.cls, e]
  ·
    intro k hk
    obtain ⟨W, hW, hn⟩ := hF.p1 k k.2 ((fixv k).1 hk)
    have hWl := htl r hr W hW
    obtain ⟨-, tf⟩ := hF.tests W hW
    refine ⟨wordElt W • CFSG.Sporadic.Fi24.root, ?_, fun e => hn ?_⟩
    · rw [fixv, root_val W hB hWl]
      exact tf
    · rw [TF_iff hB hWl, ← comm_iff]
      exact e.symm
  ·
    intro k hk hc
    have hs1 : (wordElt (wr r) • k).val = cP NW NT (wr r) k.val := sv k
    have hs2 : (wordElt (wr r) • (wordElt (wr r) • k)).val = cP NW NT (wr r ++ wr r) k.val := by
      rw [sv, sv, cP_append]
    have hmv : cP NW NT (wr r) k.val ≠ k.val := fun e => hk (by rw [fixv]; exact e)
    rcases hF.gens k k.2 hmv with ⟨p, hp, h1, h2, h3⟩ | h | ⟨d, e, hd, he, fd, fe, h1, h2, h3⟩
    · obtain ⟨p1, p2⟩ := hpl r hr p hp
      obtain ⟨-, f1, -, f2⟩ := hF.pairs p hp
      refine ⟨wordElt p.1 • CFSG.Sporadic.Fi24.root, wordElt p.2 • CFSG.Sporadic.Fi24.root, ?_, ?_,
        ?_⟩
      · rw [fixv, root_val _ hB p1]
        exact f1
      · rw [fixv, root_val _ hB p2]
        exact f2
      have ev : ((cls (wordElt p.1 • CFSG.Sporadic.Fi24.root) *
          cls (wordElt p.2 • CFSG.Sporadic.Fi24.root)) • k).val =
          cP NW NT (dW p.1 ++ dW p.2) k.val := by
        rw [mul_smul, cls_word hB p1, cls_word hB p2, cP_append]
      refine ⟨fun e' => h1 ?_, fun e' => h2 ?_, fun e' => h3 ?_⟩
      · rw [← ev, e']
      · rw [← ev, e', hs1]
      · rw [← ev, e', hs2]
    · exfalso
      apply h
      have e' := (comm_iff k (wordElt (wr r) • k)).1 hc
      rw [← hs1, ← hB.cls, e']
    · refine ⟨⟨d, hd⟩, ⟨e, he⟩, ?_, ?_, ?_⟩
      · rw [fixv]
        exact fd
      · rw [fixv]
        exact fe
      have ev : ((cls (⟨d, hd⟩ : Fin 306936) * cls (⟨e, he⟩ : Fin 306936)) • k).val =
          clsK OL NT d (clsK OL NT e k.val) := by
        rw [mul_smul, hB.cls, hB.cls]
      refine ⟨fun e' => h1 ?_, fun e' => h2 ?_, fun e' => h3 ?_⟩
      · rw [← ev, e']
      · rw [← ev, e', hs1]
      · rw [← ev, e', hs2]

theorem orbit_lvl3 (hB : Bridge) (hlv : CFSG.Perm.Native.levelLetters letters
    CFSG.Sporadic.Fi24.Native.chainBase 3 = #[12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
    Nat.card (MulAction.orbit (lvl 3) (⟨14069, by norm_num⟩ : Fin 306936)) = 1152 := by
  classical
  obtain ⟨P, hPy, hreach, hcl, hcard⟩ := lv_facts
  have hlv3 : ∀ l ∈ lv3, l < 26 := by decide
  have hxor : ∀ l ∈ lv3, l ^^^ 1 ∈ lv3 := by decide
  have hmem : ∀ l ∈ lv3, pairG gs l ∈ lvl 3 := fun l hl =>
    CFSG.Perm.lG_mem (by rw [hlv]; simpa [lv3] using hl)
  have wN_eq : ∀ v : List ℕ, (∀ l ∈ v, l < 26) → ∀ x, wN NW v x = cP NW NT v x := by
    intro v hv x
    induction v with
    | nil => rfl
    | cons l v ih =>
      change LN NW l (wN NW v x) = CF NW NT l (cP NW NT v x)
      rw [ih (fun l' h => hv l' (List.mem_cons_of_mem l h))]
      unfold CF
      rw [if_neg (by have := hv l List.mem_cons_self; omega)]
  have hinv : ∀ l ∈ lv3, ∀ x : Fin 306936, P.testBit x.val = true ↔
      P.testBit ((pairG gs l) • x).val = true := by
    intro l hl x
    have hLx := hB.letter l (hlv3 l hl) x
    constructor
    · intro hx
      have h1 := hB.letter (l ^^^ 1) (hlv3 _ (hxor l hl)) ((pairG gs l) • x)
      have e : pairG gs (l ^^^ 1) * pairG gs l = 1 := by
        have : l ^^^ 1 = invL l := by
          have := hlv3 l hl
          unfold invL
          split_ifs <;> interval_cases l <;> first | decide | omega
        rw [this, pairG_invL, inv_mul_cancel]
      rw [← mul_smul, e, one_smul] at h1
      apply hcl _ (by have := ((pairG gs l) • x).2; omega) (l ^^^ 1) (hxor l hl)
      rw [← h1]
      exact hx
    · intro hx
      apply hcl _ (by have := x.2; omega) l hl
      rw [← hLx]
      exact hx
  have horb : ∀ z : Fin 306936,
      z ∈ MulAction.orbit (lvl 3) (⟨14069, by norm_num⟩ : Fin 306936) ↔ P.testBit z.val = true := by
    intro z
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      change P.testBit (g • (⟨14069, by norm_num⟩ : Fin 306936)).val = true
      have key : ∀ x : Fin 306936, P.testBit x.val = true ↔ P.testBit (g • x).val = true := by
        unfold lvl CFSG.Perm.levelGroup CFSG.Perm.lettersGroup at hg
        rw [hlv] at hg
        induction hg using Subgroup.closure_induction with
        | mem h hh =>
          obtain ⟨l, hl, rfl⟩ := hh
          exact hinv l (by simpa [lv3] using hl)
        | one => intro x; rw [one_smul]
        | mul a b _ _ ha hb => intro x; rw [mul_smul, hb x, ha (b • x)]
        | inv a _ ha => intro x; rw [ha (a⁻¹ • x), smul_inv_smul]
      exact (key _).1 hPy
    · intro hz
      obtain ⟨v, hv, hw⟩ := hreach z.val hz
      have hvl : ∀ l ∈ v, l < 26 := fun l h => hlv3 l (hv l h)
      have hvm : wordElt v ∈ lvl 3 := by
        clear hw hz
        induction v with
        | nil => exact (lvl 3).one_mem
        | cons l v ih =>
          rw [wordElt_cons]
          exact (lvl 3).mul_mem (hmem l (hv l List.mem_cons_self))
            (ih (fun l' h => hv l' (List.mem_cons_of_mem l h))
              (fun l' h => hvl l' (List.mem_cons_of_mem l h)))
      refine ⟨⟨(wordElt v)⁻¹, (lvl 3).inv_mem hvm⟩, ?_⟩
      change (wordElt v)⁻¹ • (⟨14069, by norm_num⟩ : Fin 306936) = z
      rw [inv_smul_eq_iff]
      apply Fin.ext
      rw [word_val hB v hvl, ← wN_eq v hvl, hw]
  have hpad : ∀ x, 306936 ≤ x → x < 524288 → P.testBit x = false := by
    intro x hx1 hx2
    cases hP : P.testBit x
    · rfl
    · exfalso
      obtain ⟨v, hv, hw⟩ := hreach x hP
      have key : ∀ (v : List ℕ), (∀ l ∈ v, l ∈ lv3) → 306936 ≤ wN NW v x ∧ wN NW v x < 524288 := by
        intro v hv
        induction v with
        | nil => exact ⟨hx1, hx2⟩
        | cons l v ih =>
          obtain ⟨h1, h2⟩ := ih (fun l' h => hv l' (List.mem_cons_of_mem l h))
          change 306936 ≤ LN NW l (wN NW v x) ∧ LN NW l (wN NW v x) < 524288
          have hl := hlv3 l (hv l List.mem_cons_self)
          refine ⟨?_, LN_lt (vn.2 _) h2⟩
          by_contra hc
          unfold LN at hc
          split_ifs at hc
          · exact absurd ((CFSG.KS.Fi24Net.net_spec (nck_spec (l / 2) (by omega))).2 _ h2).1
              (by push Not at hc; omega)
          · have e := (nets (j := l / 2) (by omega) (by push Not at hc; exact hc)).1
            rw [pF_pR (vn.2 _)] at e
            omega
      have := (key v hv).1
      omega
  have hset : MulAction.orbit (lvl 3) (⟨14069, by norm_num⟩ : Fin 306936) =
      {z : Fin 306936 | P.testBit z.val = true} := Set.ext horb
  have hz : (Finset.filter (fun x => P.testBit x = true)
      (Finset.map (addLeftEmbedding 306936) (Finset.range 217352))).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hx
    rw [Finset.mem_range] at hy
    rw [hpad _ (by simp) (by simp; omega)]
    decide
  have hsplit : ((Finset.range 524288).filter fun x => P.testBit x = true).card =
      ((Finset.range 306936).filter fun x => P.testBit x = true).card := by
    rw [show (524288 : ℕ) = 306936 + 217352 by norm_num, Finset.range_add, Finset.filter_union,
      Finset.card_union_of_disjoint
        (Finset.disjoint_filter_filter (Finset.disjoint_range_addLeftEmbedding _ _)), hz, add_zero]
  have hfin : (Finset.univ.filter fun z : Fin 306936 => P.testBit z.val = true).card =
      ((Finset.range 306936).filter fun x => P.testBit x = true).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Fin.sum_univ_eq_sum_range (fun x => if P.testBit x = true then 1 else 0) 306936
  rw [hset, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_setOf, hfin, ← hsplit,
    hcard]

@[expose] noncomputable def sF : J := wordElt [2]

theorem s_val (hB : Bridge) (x : Fin 306936) : (sF • x).val = LN NW 2 x.val := by
  unfold sF
  rw [word_val hB [2] (by decide) x]
  rfl

theorem s3 (hB : Bridge) : sF ^ 3 = 1 :=
  pow3_of hB (by decide) free_facts.cube

theorem inQ_of (hB : Bridge) {x : Fin 306936} : InQN x.val ↔ InQ sF x := by
  unfold InQN InQ
  rw [← CFSG.Sporadic.FischerOddCore.cls_smul_eq_iff, ← Fin.val_eq_val, hB.cls, s_val hB]

@[expose] noncomputable def cw (v : List ℕ) : J := wordElt (invC G1 ++ (v ++ G1))

theorem cw_eq (hB : Bridge) (v : List ℕ) :
    cw v = (wordElt G1)⁻¹ * wordElt v * wordElt G1 := by
  unfold cw
  rw [wordElt_append, wordElt_append, wordElt_invC hB G1_lt, mul_assoc]

theorem cw_append (hB : Bridge) (u v : List ℕ) : cw (u ++ v) = cw u * cw v := by
  rw [cw_eq hB, cw_eq hB, cw_eq hB, wordElt_append]
  group

theorem cw_nil (hB : Bridge) : cw [] = 1 := by
  rw [cw_eq hB, wordElt_nil, mul_one, inv_mul_cancel]

theorem cw_xw (hB : Bridge) : cw xw = sF := by
  unfold xw
  rw [cw_eq hB, wordElt_append, show 2 :: invC G1 = [2] ++ invC G1 from rfl, wordElt_append,
    wordElt_invC hB G1_lt]
  unfold sF
  group

theorem cw_val (hB : Bridge) {v : List ℕ} (hv : ∀ l ∈ v, l < 26) (x : Fin 306936) :
    (cw v • x).val = cP NW NT (invC G1 ++ (v ++ G1)) x.val := by
  unfold cw
  refine word_val hB _ (fun l hl => ?_) x
  simp only [List.mem_append] at hl
  rcases hl with hl | hl | hl
  · exact invC_lt G1_lt l hl
  · exact hv l hl
  · exact G1_lt l hl

theorem eps_lt : ∀ j < 6, ∀ l ∈ nthD [] eps j, l < 26 := by decide +kernel

theorem hw_lt : ∀ w ∈ hw, ∀ l ∈ w, l < 26 := by decide +kernel

theorem swC_lt : ∀ w ∈ swC, ∀ l ∈ w, l < 26 := by decide +kernel

theorem InW_lt {ws : List (List ℕ)} (h : ∀ w ∈ ws, ∀ l ∈ w, l < 26) {v : List ℕ} (hv : InW ws v) :
    ∀ l ∈ v, l < 26 := by
  obtain ⟨L, hL, rfl⟩ := hv
  intro l hl
  obtain ⟨w, hw, hlw⟩ := List.mem_flatten.1 hl
  exact h w (hL w hw) l hlw

theorem InW_comm (hB : Bridge) {ws : List (List ℕ)} (h : ∀ w ∈ ws, cw w * sF = sF * cw w)
    {v : List ℕ} (hv : InW ws v) : cw v * sF = sF * cw v := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => rw [List.flatten_nil, cw_nil hB, one_mul, mul_one]
  | cons w L ih =>
    rw [List.flatten_cons, cw_append hB, mul_assoc,
      ih (fun w' h' => hL w' (List.mem_cons_of_mem w h')), ← mul_assoc,
      h w (hL w List.mem_cons_self), mul_assoc]

theorem base_mem (t : ℕ) (ht : t < 6) : CFSG.Sporadic.Fi24.Native.chainBase[t]! ∈ base := by
  interval_cases t <;> decide

theorem eps_comm (hB : Bridge) {j : ℕ} (hj : j < 6) : cw (nthD [] eps j) * sF = sF * cw (nthD [] eps j) := by
  apply eq_of_base
  intro t ht
  have hb := free_facts.hcomm j hj _ (base_mem t ht)
  refine Fin.ext ?_
  have hl := eps_lt j hj
  have e1 : cw (nthD [] eps j) * sF = wordElt (invC G1 ++ (nthD [] eps j ++ (G1 ++ [2]))) := by
    unfold cw sF
    simp only [wordElt_append, mul_assoc]
  have e2 : sF * cw (nthD [] eps j) = wordElt (2 :: (invC G1 ++ (nthD [] eps j ++ G1))) := by
    unfold cw sF
    rw [wordElt_cons 2 (invC G1 ++ (nthD [] eps j ++ G1)), wordElt_cons 2 [], wordElt_nil, mul_one]
  rw [e1, e2, word_val hB, word_val hB]
  · exact hb
  · intro l hl'
    rcases List.mem_cons.1 hl' with rfl | hl'
    · decide
    · simp only [List.mem_append] at hl'
      rcases hl' with h | h | h
      · exact invC_lt G1_lt l h
      · exact hl l h
      · exact G1_lt l h
  · intro l hl'
    simp only [List.mem_append, List.mem_singleton] at hl'
    rcases hl' with h | h | h | rfl
    · exact invC_lt G1_lt l h
    · exact hl l h
    · exact G1_lt l h
    · decide

theorem hw_comm (hB : Bridge) : ∀ w ∈ hw, cw w * sF = sF * cw w := by
  intro w hw'
  unfold hw at hw'
  rcases List.mem_append.1 hw' with h | h
  · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
    have hl : eps.length = 6 := rfl
    rw [← nthD_eq [] eps j hj]
    exact eps_comm hB (by rw [hl] at hj; exact hj)
  · rw [List.mem_singleton.1 h, cw_xw hB]

theorem cw_invC (hB : Bridge) {w : List ℕ} (hw : ∀ l ∈ w, l < 26) : cw (invC w) = (cw w)⁻¹ := by
  rw [cw_eq hB, cw_eq hB, wordElt_invC hB hw]
  group

theorem epsL_comm (hB : Bridge) : ∀ (l : List ℕ), (∀ i ∈ l, i < 12) →
    cw (epsL l) * sF = sF * cw (epsL l)
  | [], _ => by
    change cw [] * sF = sF * cw []
    rw [cw_nil hB, one_mul, mul_one]
  | i :: l, hl => by
    change cw (epsW i ++ epsL l) * sF = sF * cw (epsW i ++ epsL l)
    have ih := epsL_comm hB l (fun i' h => hl i' (List.mem_cons_of_mem i h))
    have hi : cw (epsW i) * sF = sF * cw (epsW i) := by
      have hi12 := hl i List.mem_cons_self
      by_cases h6 : i < 6
      · have e : epsW i = nthD [] eps i := by
          unfold epsW
          rw [blt_of h6]
        rw [e]
        exact eps_comm hB h6
      · have e : epsW i = invC (nthD [] eps (i - 6)) := by
          unfold epsW
          have : Nat.blt i 6 = false := by
            cases h : Nat.blt i 6
            · rfl
            · exact absurd (blt_t h) h6
          rw [this]
          rfl
        rw [e, cw_invC hB (eps_lt (i - 6) (by omega))]
        exact comm_inv' (eps_comm hB (j := i - 6) (by omega))
    rw [cw_append hB, mul_assoc, ih, ← mul_assoc, hi, mul_assoc]

theorem swC_eq : swC = [epsL (nthD [] sw 0), epsL (nthD [] sw 1), xw] := by decide +kernel

theorem sw_lt : (∀ i ∈ nthD [] sw 0, i < 12) ∧ ∀ i ∈ nthD [] sw 1, i < 12 := by decide +kernel

theorem swC_comm (hB : Bridge) : ∀ w ∈ swC, cw w * sF = sF * cw w := by
  intro w hw
  rw [swC_eq] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact epsL_comm hB _ sw_lt.1
  · exact epsL_comm hB _ sw_lt.2
  · rw [cw_xw hB]

@[expose] def d0 : Fin 306936 := ⟨12, by norm_num⟩

theorem pq_pull (hB : Bridge) {v : List ℕ} (hv : InW hw v) (x : Fin 306936) :
    PQ.testBit (cw v • x).val = true → PQ.testBit x.val = true := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L generalizing x with
  | nil => rw [List.flatten_nil, cw_nil hB, one_smul]; exact id
  | cons w L ih =>
    intro h
    rw [List.flatten_cons, cw_append hB, mul_smul] at h
    have hw' := hL w List.mem_cons_self
    have h1 := free_facts.qcl _ (cw (L.flatten) • x).2 w hw' (by rw [← cw_val hB (hw_lt w hw')]; exact h)
    exact ih x (fun w' h' => hL w' (List.mem_cons_of_mem w h')) h1

theorem pull_pow {n : J} {P : Fin 306936 → Prop} (h : ∀ y, P (n • y) → P y) :
    ∀ k y, P (n ^ k • y) → P y
  | 0, y, hy => by rwa [pow_zero, one_smul] at hy
  | k + 1, y, hy => by
    rw [pow_succ, mul_smul] at hy
    exact h y (pull_pow h k _ hy)

theorem push_of_pull {n : J} {P : Fin 306936 → Prop} (h : ∀ y, P (n • y) → P y) (y : Fin 306936)
    (hy : P y) : P (n • y) := by
  have hm := orderOf_pos n
  have e : n ^ (orderOf n - 1) • (n • y) = y := by
    rw [← mul_smul, ← pow_succ, Nat.sub_add_cancel hm, pow_orderOf_eq_one, one_smul]
  exact pull_pow h _ _ (by rw [e]; exact hy)

theorem hr_mem {r : ℕ} (hrm : r ∈ hr) : ∃ i < 12, r = nthD 0 hr i := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hrm
  have hl := free_facts.hr_len
  exact ⟨i, by rw [hl] at hi; exact hi, (nthD_eq 0 hr i hi).symm⟩

theorem pq_iff (hB : Bridge) (x : Fin 306936) : PQ.testBit x.val = true ↔ InQ sF x := by
  obtain ⟨v, hv, hr⟩ := free_facts.hcov x.val x.2
  have hvl := InW_lt hw_lt hv
  rw [← cw_val hB hvl] at hr
  obtain ⟨i, hi, hri⟩ := hr_mem hr
  have hn := InW_comm hB (hw_comm hB) hv
  have hn' : (cw v)⁻¹ * sF = sF * (cw v)⁻¹ := comm_inv' hn
  constructor
  · intro hP
    have h1 : PQ.testBit (cw v • x).val = true :=
      push_of_pull (P := fun y => PQ.testBit y.val = true) (fun y => pq_pull hB hv y) x hP
    rw [hri] at h1
    have hi3 : i < 3 := by
      by_contra hc
      rw [((free_facts.hq i hi).2 (by omega)).1] at h1
      exact absurd h1 (by decide)
    have hq := ((free_facts.hq i hi).1 hi3).2
    rw [← hri, inQ_of hB] at hq
    have := InQ.of_commute hn' hq
    rwa [inv_smul_smul] at this
  · intro hq
    have h1 := InQ.of_commute hn hq
    rw [← inQ_of hB, hri] at h1
    have hi3 : i < 3 := by
      by_contra hc
      exact ((free_facts.hq i hi).2 (by omega)).2 h1
    have h2 := ((free_facts.hq i hi).1 hi3).1
    rw [← hri] at h2
    exact pq_pull hB hv x h2

theorem uR_val (hB : Bridge) (y q : Fin 306936) :
    (uR sF y • q).val = uP NW OL NT y.val q.val := by
  unfold uR
  rw [mul_smul, mul_smul, hB.cls, hB.cls, hB.cls, s_val hB, s_val hB, s_val hB, uP_eq]

theorem uR_pow_val (hB : Bridge) (f : ℕ → ℕ) (g : R) (hg : ∀ q : Fin 306936, (g • q).val = f q.val) :
    ∀ n (q : Fin 306936), (g ^ n • q).val = f^[n] q.val
  | 0, q => by rw [pow_zero, one_smul]; rfl
  | n + 1, q => by
    rw [pow_succ', mul_smul, hg, uR_pow_val hB f g hg n q, Function.iterate_succ_apply']

theorem three_dvd_of_cycle (hB : Bridge) {f : ℕ → ℕ} {g : R}
    (hg : ∀ q : Fin 306936, (g • q).val = f q.val) {p L : ℕ} (hp : p < 306936)
    (h : L % 3 = 0 ∧ L ≠ 0 ∧ f^[L] p = p ∧ f^[L / 3] p ≠ p) : 3 ∣ orderOf g := by
  obtain ⟨h1, -, h3, h4⟩ := h
  refine three_dvd_orderOf_of_smul_cycle g (⟨p, hp⟩ : Fin 306936) (Nat.dvd_of_mod_eq_zero h1) ?_ ?_
  · apply Fin.ext
    rw [uR_pow_val hB f g hg]
    exact h3
  · intro e
    apply h4
    have := congrArg Fin.val e
    rwa [uR_pow_val hB f g hg] at this

@[expose] def InTri (y : Fin 306936) : Prop := ∃ a : ℕ, y = sF ^ a • d0

theorem inTri_mul {n m : J} (hn : n * sF = sF * n) (h1 : InTri (n • d0)) (h2 : InTri (m • d0)) :
    InTri ((n * m) • d0) := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  refine ⟨b + a, ?_⟩
  rw [mul_smul, hb, ← mul_smul, comm_pow' hn b, mul_smul, ha, ← mul_smul, ← pow_add]

theorem cst_tri (hB : Bridge) {w : List ℕ} (hw : w ∈ swC) : InTri (cw w • d0) := by
  have h := free_facts.cst w hw
  have hl := swC_lt w hw
  have e : (cw w • d0).val = cP NW NT (invC G1 ++ (w ++ G1)) 12 := cw_val hB hl d0
  rcases h with h | h | h
  · exact ⟨0, Fin.ext (by rw [e, h, pow_zero, one_smul]; rfl)⟩
  · exact ⟨1, Fin.ext (by rw [e, h, pow_one, s_val hB]; rfl)⟩
  · exact ⟨2, Fin.ext (by rw [e, h, pow_two, mul_smul, s_val hB, s_val hB]; rfl)⟩

theorem InW_tri (hB : Bridge) {v : List ℕ} (hv : InW swC v) : InTri (cw v • d0) := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => exact ⟨0, by rw [List.flatten_nil, cw_nil hB, one_smul, pow_zero, one_smul]⟩
  | cons w L ih =>
    rw [List.flatten_cons, cw_append hB]
    exact inTri_mul (swC_comm hB w (hL w List.mem_cons_self)) (cst_tri hB (hL w List.mem_cons_self))
      (ih (fun w' h' => hL w' (List.mem_cons_of_mem w h')))

theorem tri_of (hB : Bridge) {y : Fin 306936} (h : InTri y) :
    y = d0 ∨ y = sF • d0 ∨ y = sF • (sF • d0) := by
  obtain ⟨a, rfl⟩ := h
  have e : sF ^ a = sF ^ (a % 3) := by
    conv_lhs => rw [← Nat.div_add_mod a 3, pow_add, pow_mul, s3 hB, one_pow, one_mul]
  rw [e]
  have : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 3)
  · exact Or.inl (by rw [pow_zero, one_smul])
  · exact Or.inr (Or.inl (by rw [pow_one]))
  · exact Or.inr (Or.inr (by rw [pow_two, mul_smul]))

theorem uR_tri (hB : Bridge) (hq : InQ sF d0) {y : Fin 306936} (h : InTri y) : uR sF y = uR sF d0 := by
  rcases tri_of hB h with rfl | rfl | rfl
  · rfl
  · exact uR_smul (s3 hB) hq
  · rw [uR_smul (s3 hB) hq.smul, uR_smul (s3 hB) hq]

theorem d0_Q (hB : Bridge) : InQ sF d0 := by
  have h := ((free_facts.hq 0 (by decide)).1 (by decide)).2
  rw [free_facts.lks.1] at h
  exact (inQ_of hB).1 h

theorem crx_mem {z : ℕ} (h : z ∈ crx) : ∃ c ∈ cr, c.1 = z := by
  have key : ∀ (l : List (ℕ × ℕ × ℕ × ℕ)),
      z ∈ List.rec (motive := fun _ => List ℕ) [] (fun c _ ih => c.1 :: ih) l → ∃ c ∈ l, c.1 = z := by
    intro l
    induction l with
    | nil => intro h'; exact absurd h' List.not_mem_nil
    | cons c l ih =>
      intro h'
      rcases List.mem_cons.1 h' with e | e
      · exact ⟨c, List.mem_cons_self, e.symm⟩
      · obtain ⟨c', hc', e'⟩ := ih e
        exact ⟨c', List.mem_cons_of_mem c hc', e'⟩
  exact key cr h

theorem cr_pts : ∀ c ∈ cr, c.2.1 < 306936 ∧ c.2.2.2 ≤ 306936 := by decide +kernel

theorem crit_all (hB : Bridge) {x : Fin 306936} (hxQ : InQ sF x) (h0 : x ≠ d0) (h1 : x ≠ sF • d0)
    (h2 : x ≠ sF • (sF • d0)) :
    3 ∣ orderOf (uR sF d0 * uR sF x) ∨ ∃ k : Fin 306936, InQ sF k ∧
      3 ∣ orderOf (uR sF d0 * uR sF x * uR sF k * uR sF d0 * uR sF x * uR sF k) := by
  have hP := (pq_iff hB x).2 hxQ
  have hx0 : x.val ≠ 12 := fun e => h0 (Fin.ext e)
  have hx1 : x.val ≠ LN NW 2 12 := fun e => h1 (Fin.ext (by rw [e, s_val hB]; rfl))
  have hx2 : x.val ≠ LN NW 2 (LN NW 2 12) := fun e => h2 (Fin.ext (by rw [e, s_val hB, s_val hB]; rfl))
  obtain ⟨v, hv, hz⟩ := free_facts.ccov x.val x.2 hP hx0 hx1 hx2
  have hvl := InW_lt swC_lt hv
  set n := cw v with hn_def
  have hn : n * sF = sF * n := InW_comm hB (swC_comm hB) hv
  have hn' : n⁻¹ * sF = sF * n⁻¹ := comm_inv' hn
  have htri : InTri (n • d0) := InW_tri hB hv
  set z := n • x with hz_def
  have hzv : z.val = cP NW NT (invC G1 ++ (v ++ G1)) x.val := cw_val hB hvl x
  rw [← hzv] at hz
  have hzQ : InQ sF z := InQ.of_commute hn hxQ
  have hzt : ¬ InTri z := by
    rintro ⟨a, ha⟩
    obtain ⟨b, hb⟩ := htri
    apply (show ¬ InTri x from fun ⟨c, hc⟩ => by
      rcases tri_of hB ⟨c, hc⟩ with e | e | e
      · exact h0 e
      · exact h1 e
      · exact h2 e)
    refine ⟨a + 2 * b, ?_⟩
    have e1 : x = n⁻¹ • (sF ^ a • d0) := by rw [← ha, hz_def, inv_smul_smul]
    have hc : ∀ k : ℕ, n⁻¹ * sF ^ k = sF ^ k * n⁻¹ := fun k =>
      comm_pow' hn' k
    have hb' : sF ^ b • (n⁻¹ • d0) = d0 := by
      rw [← mul_smul, ← hc, mul_smul, ← hb, inv_smul_smul]
    have e2 : n⁻¹ • d0 = sF ^ (2 * b) • d0 := by
      have h3b : sF ^ (2 * b) * sF ^ b = 1 := by
        rw [← pow_add, show 2 * b + b = 3 * b by ring, pow_mul, s3 hB, one_pow]
      conv_rhs => rw [← hb', ← mul_smul, h3b, one_smul]
    rw [e1, ← mul_smul, hc, mul_smul, e2, ← mul_smul, ← pow_add]
  have hu0 : uR sF d0 = jR n * uR sF d0 * (jR n)⁻¹ := by
    rw [conj_uR hn, uR_tri hB (d0_Q hB) htri]
  have hux : uR sF z = jR n * uR sF x * (jR n)⁻¹ := (conj_uR hn x).symm
  have hord : ∀ y : R, orderOf (jR n * y * (jR n)⁻¹) = orderOf y := fun y =>
    MulEquiv.orderOf_eq (MulAut.conj (jR n)) y
  rcases hz with hz | hz
  · obtain ⟨c, hc, hcz⟩ := crx_mem hz
    obtain ⟨hp, -⟩ := cr_pts c hc
    obtain ⟨t1, t2⟩ := free_facts.ct c hc
    by_cases hk : c.2.2.2 = 306936
    · left
      have key := three_dvd_of_cycle hB (g := uR sF d0 * uR sF z)
        (f := fun q => uP NW OL NT 12 (uP NW OL NT c.1 q))
        (fun q => by rw [mul_smul, uR_val hB, uR_val hB, hcz]; rfl) hp (t1 hk)
      rw [hu0, hux, show jR n * uR sF d0 * (jR n)⁻¹ * (jR n * uR sF x * (jR n)⁻¹) =
        jR n * (uR sF d0 * uR sF x) * (jR n)⁻¹ by group, hord] at key
      exact key
    · right
      obtain ⟨hkq, t2⟩ := t2 hk
      have hk' : c.2.2.2 < 306936 := lt_of_le_of_ne (cr_pts c hc).2 hk
      set k' : Fin 306936 := ⟨c.2.2.2, hk'⟩
      have hk'Q : InQ sF k' := (pq_iff hB k').1 hkq
      refine ⟨n⁻¹ • k', by simpa using InQ.of_commute hn' hk'Q, ?_⟩
      have huk : uR sF k' = jR n * uR sF (n⁻¹ • k') * (jR n)⁻¹ := by
        rw [conj_uR hn, smul_inv_smul]
      have key := three_dvd_of_cycle hB
        (g := uR sF d0 * uR sF z * uR sF k' * uR sF d0 * uR sF z * uR sF k')
        (f := fun q => uP NW OL NT 12 (uP NW OL NT c.1 (uP NW OL NT c.2.2.2
          (uP NW OL NT 12 (uP NW OL NT c.1 (uP NW OL NT c.2.2.2 q))))))
        (fun q => by
          simp only [mul_smul]
          rw [uR_val hB, uR_val hB, uR_val hB, uR_val hB, uR_val hB, uR_val hB, hcz]
          rfl)
        hp t2
      rw [hu0, hux, huk] at key
      rw [← hord (uR sF d0 * uR sF x * uR sF (n⁻¹ • k') * uR sF d0 * uR sF x * uR sF (n⁻¹ • k'))]
      convert key using 2
      group
  · exfalso
    rcases cF_bit hz with h' | h' | h' | h' | h'
    · exact h' z.2
    · rw [(pq_iff hB z).2 hzQ] at h'
      exact absurd h' (by decide)
    · exact hzt ⟨0, Fin.ext (by rw [h', pow_zero, one_smul]; rfl)⟩
    · exact hzt ⟨1, Fin.ext (by rw [h', pow_one, s_val hB]; rfl)⟩
    · exact hzt ⟨2, Fin.ext (by rw [h', pow_two, mul_smul, s_val hB, s_val hB]; rfl)⟩

theorem lk_lt : nthD 0 lk 0 < 306936 ∧ nthD 0 lk 1 < 306936 := by decide +kernel

@[expose] noncomputable def HQ : Subgroup R :=
  Subgroup.closure ((Set.range fun j : Fin 6 => jR (cw (nthD [] eps j))) ∪ {jR sF} ∪
    {uR sF ⟨nthD 0 lk 0, lk_lt.1⟩, uR sF ⟨nthD 0 lk 1, lk_lt.2⟩})

theorem lk_Q (hB : Bridge) (i : ℕ) (hi : i < 2) (h : nthD 0 lk i < 306936) :
    InQ sF ⟨nthD 0 lk i, h⟩ :=
  (pq_iff hB _).1 (free_facts.lks.2 i hi).1

theorem HQ_comm (hB : Bridge) : ∀ g ∈ HQ, g * jR sF = jR sF * g := by
  intro g hg
  have hle : HQ ≤ Subgroup.centralizer {jR sF} := by
    apply (Subgroup.closure_le _).2
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hy with (⟨j, rfl⟩ | hy) | hy
    · rw [← map_mul, ← map_mul, eps_comm hB j.2]
    · rw [Set.mem_singleton_iff.1 hy]
    · rcases hy with rfl | hy
      · exact uR_commute (s3 hB) (lk_Q hB 0 (by decide) lk_lt.1)
      · rw [Set.mem_singleton_iff.1 hy]
        exact uR_commute (s3 hB) (lk_Q hB 1 (by decide) lk_lt.2)
  have := hle hg
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem cw_mem (hB : Bridge) {v : List ℕ} (hv : InW hw v) : jR (cw v) ∈ HQ := by
  obtain ⟨L, hL, rfl⟩ := hv
  induction L with
  | nil => rw [List.flatten_nil, cw_nil hB, map_one]; exact (HQ).one_mem
  | cons w L ih =>
    rw [List.flatten_cons, cw_append hB, map_mul]
    refine (HQ).mul_mem ?_ (ih fun w' h' => hL w' (List.mem_cons_of_mem w h'))
    have hw' := hL w List.mem_cons_self
    unfold hw at hw'
    rcases List.mem_append.1 hw' with h | h
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 h
      have hl : eps.length = 6 := rfl
      rw [← nthD_eq [] eps j hj]
      exact Subgroup.subset_closure (Or.inl (Or.inl ⟨⟨j, by rw [hl] at hj; exact hj⟩, rfl⟩))
    · rw [List.mem_singleton.1 h, cw_xw hB]
      exact Subgroup.subset_closure (Or.inl (Or.inr rfl))

theorem orbit_of (hB : Bridge) (x : Fin 306936) (hx : InQ sF x) : ∃ g ∈ HQ, g • d0 = x := by
  obtain ⟨v, hv, hr⟩ := free_facts.hcov x.val x.2
  have hvl := InW_lt hw_lt hv
  rw [← cw_val hB hvl] at hr
  obtain ⟨i, hi, hri⟩ := hr_mem hr
  have hn := InW_comm hB (hw_comm hB) hv
  have h1 := InQ.of_commute hn hx
  rw [← inQ_of hB, hri] at h1
  have hi3 : i < 3 := by
    by_contra hc
    exact ((free_facts.hq i hi).2 (by omega)).2 h1
  have hn_mem := (HQ).inv_mem (cw_mem hB hv)
  have l0 := (free_facts.lks.2 0 (by decide)).2
  have l1 := (free_facts.lks.2 1 (by decide)).2
  interval_cases i
  · refine ⟨jR (cw v)⁻¹, by rwa [map_inv], ?_⟩
    rw [CFSG.Sporadic.Fi24.jR_smul, inv_smul_eq_iff]
    apply Fin.ext
    rw [hri, free_facts.lks.1]
    rfl
  · refine ⟨jR (cw v)⁻¹ * uR sF ⟨nthD 0 lk 0, lk_lt.1⟩, (HQ).mul_mem (by rwa [map_inv])
      (Subgroup.subset_closure (Or.inr (Or.inl rfl))), ?_⟩
    rw [mul_smul, CFSG.Sporadic.Fi24.jR_smul, inv_smul_eq_iff]
    apply Fin.ext
    rw [hri, uR_val hB]
    exact l0
  · refine ⟨jR (cw v)⁻¹ * uR sF ⟨nthD 0 lk 1, lk_lt.2⟩, (HQ).mul_mem (by rwa [map_inv])
      (Subgroup.subset_closure (Or.inr (Or.inr rfl))), ?_⟩
    rw [mul_smul, CFSG.Sporadic.Fi24.jR_smul, inv_smul_eq_iff]
    apply Fin.ext
    rw [hri, uR_val hB]
    exact l1

theorem uR_word (hB : Bridge) {W : List ℕ} (hW : ∀ l ∈ W, l < 26) (y : Fin 306936) :
    (uR sF (wordElt W • CFSG.Sporadic.Fi24.root) • y).val = cP NW NT (uC W) y.val := by
  have hs : sF = pairG gs 2 := by
    unfold sF
    rw [wordElt_cons, wordElt_nil, mul_one]
  have e1 : sF • (wordElt W • CFSG.Sporadic.Fi24.root) = wordElt (2 :: W) • CFSG.Sporadic.Fi24.root := by
    rw [← mul_smul, wordElt_cons, hs]
  have e2 : sF • (wordElt (2 :: W) • CFSG.Sporadic.Fi24.root) =
      wordElt (2 :: 2 :: W) • CFSG.Sporadic.Fi24.root := by
    rw [← mul_smul, wordElt_cons 2 (2 :: W), hs]
  have h2 : ∀ l ∈ 2 :: W, l < 26 := fun l h => by
    rcases List.mem_cons.1 h with rfl | h
    · decide
    · exact hW l h
  have h3 : ∀ l ∈ 2 :: 2 :: W, l < 26 := fun l h => by
    rcases List.mem_cons.1 h with rfl | h
    · decide
    · exact h2 l h
  unfold uR uC
  rw [e1, e2, mul_smul, mul_smul, cls_word hB hW, cls_word hB h2, cls_word hB h3, cP_append,
    cP_append]

theorem bk_lt : (∀ l ∈ bk, l < 26) ∧ ∀ l ∈ bl, l < 26 := by decide +kernel

theorem freeFacts_of (hB : Bridge) : FreeFacts [2] d0 := by
  have hF := free_facts
  have hs : wordElt [2] = sF := rfl
  refine ⟨fun l hl => by rw [letters_size26, List.mem_singleton.1 hl]; decide, s3 hB, ?_, d0_Q hB,
    ⟨HQ, HQ_comm hB, orbit_of hB⟩, fun x hx h0 h1 h2 _ _ => crit_all hB hx h0 h1 h2, ?_, ?_⟩
  · intro k e
    apply hF.fpf k.val k.2
    rw [← Fin.val_eq_val] at e
    rw [← word_val hB [2] (by decide), e]
  · intro i hi
    obtain ⟨b1, b2, b3⟩ := hF.bs i hi
    refine ⟨⟨_, free_facts.pq_pts _ b1⟩, ⟨_, free_facts.pq_pts _ b2⟩, (pq_iff hB _).1 b1,
      (pq_iff hB _).1 b2, ?_⟩
    rw [hB.cls, b3, chainBase_eq]
    interval_cases i <;> rfl
  · have hk : (wordElt bk • CFSG.Sporadic.Fi24.root).val = cP NW NT bk 0 := root_val bk hB bk_lt.1
    have hl : (wordElt bl • CFSG.Sporadic.Fi24.root).val = cP NW NT bl 0 := root_val bl hB bk_lt.2
    refine ⟨wordElt bk • CFSG.Sporadic.Fi24.root, wordElt bl • CFSG.Sporadic.Fi24.root,
      (pq_iff hB _).1 (by rw [hk]; exact hF.bg.1), (pq_iff hB _).1 (by rw [hl]; exact hF.bg.2.1),
      fun x hx => ?_⟩
    obtain ⟨o1, o2, o3⟩ := hF.bg.2.2 x.val x.2 ((pq_iff hB x).2 hx)
    have ev : ((uR sF (wordElt bk • CFSG.Sporadic.Fi24.root) *
        uR sF (wordElt bl • CFSG.Sporadic.Fi24.root)) • x).val = cP NW NT (uC bk ++ uC bl) x.val := by
      rw [mul_smul, uR_word hB bk_lt.1, uR_word hB bk_lt.2, cP_append]
    rw [hs]
    refine ⟨fun e => o1 ?_, fun e => o2 ?_, fun e => o3 ?_⟩
    · rw [← ev, e]
    · rw [← ev, e, s_val hB]
      rfl
    · rw [← ev, e, s_val hB, s_val hB]
      rfl

end CFSG.KD.Fi24ThreeO.Group

end
