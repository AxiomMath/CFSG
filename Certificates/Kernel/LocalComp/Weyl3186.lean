module

public import Certificates.Kernel.LocalComp.Weyl3186K
public import Certificates.Kernel.LocalComp.Weyl3187
public import CFSG.Certificates.Kernel.LocalCompSPSound
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylTData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3186

open CFSG.KC.Enum CFSG.KS CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelLC
open CFSG.RankThree.Native (rep_of_eqA permOfArr_eq_of_rep)

attribute [local irreducible] okC spMul

theorem kRD : rootsDK E8.RK E8.DP = true := by quickRfl

theorem hSP : SPBind rootList keyPts E8.RK E8.RT E8.ST E8.FT E8.PT E8.SO E8.NEG E8.FR E8.DP
    W3220.KP :=
  ⟨E8.bind, E8.sorted, E8.hrt, E8.neg, E8.hst, E8.froots, E8.ft0, E8.hft, W3187.kHF,
    W3189.kPairs, W3189.k5, W3220.kKP, W3187.kL, kRD⟩

theorem dpk : DPK = E8.DP := by decide +kernel

@[expose] noncomputable def Φ (c : ℕ) : Equiv.Perm (Fin 240) := permOfArr 240 (spArrC rootList c)

theorem rep_Φ {c : ℕ} (hc : okC c = true) : Rep 240 (spArrC rootList c) (Φ c) :=
  (rep_permOfArr (spC_valid hSP hc)).1

theorem Φ_mul {a b : ℕ} (ha : okC a = true) (hb : okC b = true) : Φ a * Φ b = Φ (spMul a b) := by
  have h := rep_compA (rep_Φ ha) (rep_Φ hb)
  rw [spC_mul hSP ha hb] at h
  exact (permOfArr_eq_of_rep h).symm

theorem Φ_inj {a b : ℕ} (ha : okC a = true) (hb : okC b = true) (h : Φ a = Φ b) : a = b :=
  spC_inj hSP ha hb ((eqA_iff (rep_Φ ha) (rep_Φ hb)).2 h)

theorem eqA_comm' {n : ℕ} {t u : Array ℕ} (h : eqA n t u = true) : eqA n u t = true := by
  rw [eqA, allLt_iff] at h ⊢
  intro i hi
  have := h i hi
  rw [beq_iff_eq] at this ⊢
  exact this.symm

theorem rep_of_eqA' {x y : Array ℕ} {X : Equiv.Perm (Fin 240)} (hy : Rep 240 y X)
    (h : eqA 240 x y = true) : Rep 240 x X :=
  rep_of_eqA hy (eqA_comm' h)

theorem isInvA_of_reps {t r : Array ℕ} {X : Equiv.Perm (Fin 240)} (ht : Rep 240 t X)
    (hr : Rep 240 r X⁻¹) : isInvA 240 t r = true := by
  rw [isInvA, allLt_iff]
  intro i hi
  have h1 := ht ⟨i, hi⟩
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨by rw [h1]; exact (X ⟨i, hi⟩).2, ?_⟩
  rw [h1, hr (X ⟨i, hi⟩)]
  simp

theorem invCand_eq_foldl' (n : ℕ) (t : Array ℕ) :
    invCand n t = (List.range n).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0) := by
  unfold invCand
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl,
    Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure, List.range_eq_range']
  rfl

theorem rep_invCand' {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    Rep n (invCand n t) g⁻¹ := by
  have key : ∀ k ≤ n, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0)).size = n ∧ ∀ i < k, ((List.range k).foldl (fun r i => r.set! t[i]! i)
      (Array.replicate n 0))[t[i]!]! = i := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨hs, hi⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set r := (List.range k).foldl (fun r i => r.set! t[i]! i) (Array.replicate n 0)
      have htk : t[k]! < n := ht.lt (by omega)
      refine ⟨by rw [Array.size_set!, hs], fun i hik => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hik with hlt | rfl
      · have hne : t[i]! ≠ t[k]! := by
          intro e
          rw [ht.apply (by omega : i < n), ht.apply (by omega : k < n)] at e
          have := g.injective (Fin.ext e)
          simp at this
          omega
        rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hne)]
        exact hi i hlt
      · rw [Array.getElem!_set!_self _ _ _ (by rw [hs]; exact htk)]
  intro x
  obtain ⟨hs, hi⟩ := key n le_rfl
  rw [invCand_eq_foldl']
  have e : t[(g⁻¹ x : Fin n).val]! = x.val := by
    rw [ht.apply (g⁻¹ x).2]
    simp
  rw [← e, hi _ (g⁻¹ x).2]

theorem isInvA_of_rep {t : Array ℕ} {X : Equiv.Perm (Fin 240)} (ht : Rep 240 t X) :
    isInvA 240 t (invCand 240 t) = true :=
  isInvA_of_reps ht (rep_invCand' ht)

theorem gens_facts : (∀ k < 13, okC (e32 GC k) = true ∧ spMul (e32 GC k) (e32 GC k) = spId) ∧
    okC s0C = true ∧ okC negC = true ∧ okC spId = true ∧
    ∀ k < 25, okC (e32 RH k) = true ∧ okC (e32 RHI k) = true ∧
      spMul (e32 RH k) (e32 RHI k) = spId := by
  have h := kGens
  simp only [gensK, bAnd_eq, strictB_eq', Bool.and_eq_true, allN_iff, invoK, Nat.beq_eq] at h
  exact h

theorem range_all {f : ℕ → Bool} (h : ∀ q < 16, rangeK f (512 * q) 512 = true) :
    ∀ i < 8192, f i = true := by
  intro i hi
  have h1 := allN_spec (h (i / 512) (by omega)) (i % 512) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (512 * (i / 512)) (i % 512) = i := by
    simp only [Nat.add_eq]
    omega
  rwa [e] at h1

theorem closed_facts {i : ℕ} (hi : i < 8192) : okC (tcK PP i) = true ∧ ∀ k < 13,
    jdxK PP MT GC i k < 8192 ∧ tcK PP (jdxK PP MT GC i k) = spMul (e32 GC k) (tcK PP i) := by
  have h := range_all kC i hi
  simp only [closedAt, bAnd_eq, strictB_eq', Bool.and_eq_true, allN_iff, Nat.beq_eq,
    Nat.blt_eq] at h
  exact h

theorem okTC {i : ℕ} (hi : i < 8192) : okC (tcK PP i) = true := (closed_facts hi).1

theorem tree_facts {i : ℕ} (hi : i < 8192) (hpos : 0 < i) : ∃ k < 13,
    jdxK PP MT GC i k < i ∧ spMul (e32 GC k) (tcK PP (jdxK PP MT GC i k)) = tcK PP i := by
  have h := range_all kT i hi
  have hne : Nat.beq i 0 = false := by
    rcases i with _ | i
    · omega
    · rfl
  simp only [treeAt, bIf_eq, hne] at h
  obtain ⟨k, hk, hk'⟩ := not_allN h
  simp only [strictB_eq', notB'_eq, Bool.not_eq_false'] at hk'
  split at hk'
  · next hb =>
    exact ⟨k, hk, by simpa using hb, Nat.eq_of_beq_eq_true hk'⟩
  · exact absurd hk' (by decide)

theorem kPPL : ∀ p < 64, codeL (e24 PP p) = pPlusImgs.getD p [] := by decide +kernel

theorem kPPinj : ∀ p < 64, ∀ q < 64, pPlusImgs.getD p [] = pPlusImgs.getD q [] → p = q := by
  decide +kernel

theorem tElt_eq {i : ℕ} (hi : i < 8192) :
    tElt tPlusCert i false = spArrC rootList (tcK PP i) := by
  simp only [tElt, Bool.false_eq_true, ite_false, tPlusCert]
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, spArrC, tcK_mask, tcK_list,
    kPPL (i / 128) (by omega), evenMaskK_eq, spArr_eq]
  rfl

theorem rep_tElt {i : ℕ} (hi : i < 8192) : Rep 240 (tElt tPlusCert i false) (Φ (tcK PP i)) := by
  rw [tElt_eq hi]
  exact rep_Φ (okTC hi)

theorem tcK_inj {i j : ℕ} (hi : i < 8192) (hj : j < 8192) (h : tcK PP i = tcK PP j) : i = j := by
  have hm := congrArg spMask h
  have hl := congrArg codeL h
  rw [tcK_mask, tcK_mask, evenMaskK_eq, evenMaskK_eq] at hm
  rw [tcK_list, tcK_list, kPPL _ (by omega), kPPL _ (by omega)] at hl
  have h1 := kPPinj _ (by omega) _ (by omega) hl
  have h2 : i % 128 = j % 128 := by
    have := Nat.mod_lt (framePop (i % 128)) (show 0 < 2 by norm_num)
    have := Nat.mod_lt (framePop (j % 128)) (show 0 < 2 by norm_num)
    omega
  omega

theorem Φ_id : Φ spId = 1 := (eqA_iff (rep_Φ gens_facts.2.2.2.1) rep_idA).1 (spC_one hSP)

theorem rep_negArr' : Rep 240 negArr (Φ negC) :=
  rep_of_eqA' (rep_Φ gens_facts.2.2.1) (eqA_comm' (spC_neg hSP))

theorem refl1 : reflCodeK E8.DP 1 = s0C := by decide +kernel

theorem rep_s0Arr' : Rep 240 s0Arr (Φ s0C) := by
  have h := spC_refl hSP (r := 1) (by norm_num)
  rw [refl1] at h
  exact rep_of_eqA' (rep_Φ gens_facts.2.1) h

theorem rep_tElt_true {i : ℕ} (hi : i < 8192) :
    Rep 240 (tElt tPlusCert i true) (Φ (spMul (tcK PP i) s0C)) := by
  have h := rep_compA (rep_tElt hi) rep_s0Arr'
  rw [Φ_mul (okTC hi) gens_facts.2.1] at h
  simpa [tElt] using h

theorem isId_iff' {x : Array ℕ} {X : Equiv.Perm (Fin 240)} (hx : Rep 240 x X) :
    isId x = true ↔ X = 1 := eqA_iff hx rep_idA

theorem eqId {c : ℕ} (hc : okC c = true) {x : Array ℕ} (hx : Rep 240 x (Φ c)) :
    isId x = true ↔ c = spId := by
  rw [isId_iff' hx, ← Φ_id]
  exact ⟨Φ_inj hc gens_facts.2.2.2.1, fun h => h ▸ rfl⟩

theorem eqNeg {c : ℕ} (hc : okC c = true) {x : Array ℕ} (hx : Rep 240 x (Φ c)) :
    eqA 240 x negArr = true ↔ c = negC := by
  rw [eqA_iff hx rep_negArr']
  exact ⟨Φ_inj hc gens_facts.2.2.1, fun h => h ▸ rfl⟩

theorem tPlusGensArr_sign' {k : ℕ} (hk : k < 7) :
    tPlusGensArr[k]! = signArr (frameDecode (1 + 2 ^ (k + 1))) := by
  rw [tPlusGensArr, getElem!_pos _ k (by simp [pPlusGens]; omega)]
  simp only [List.getElem_toArray]
  rw [List.getElem_append_left (by simpa using hk)]
  simp

theorem tPlusGensArr_perm' {k : ℕ} (hk : k < 6) :
    tPlusGensArr[7 + k]! = permArr (pPlusGens.getD k 1) := by
  rw [tPlusGensArr, getElem!_pos _ (7 + k) (by simp [pPlusGens]; omega)]
  simp only [List.getElem_toArray]
  rw [List.getElem_append_right (by simp)]
  simp only [List.length_map, List.length_range, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa [pPlusGens] using hk)]
  congr 2
  omega

theorem signArrsL_get {m : ℕ} (hm : m < 256) :
    (signArrsL rootList)[m]! = signArr (frameDecode m) := by
  rw [signArrsL, getElem!_pos _ m (by simpa using hm)]
  simp [signArr_eq]

theorem permArr_eq_listPermArr (σ : Equiv.Perm (Fin 8)) (l : List ℕ)
    (h : ∀ j : Fin 8, (σ.symm j : ℕ) = l.idxOf (j : ℕ)) : permArr σ = listPermArr l := by
  unfold permArr listPermArr listPermVec
  congr 1
  funext i
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  rw [h]
  rfl

theorem gen_codes : (∀ k < 7, e32 GC k = (1 + 2 ^ (k + 1)) * 2 ^ 24 + spId) ∧
    ∀ k < 6, spMask (e32 GC (7 + k)) = 0 ∧ codeL (e32 GC (7 + k)) =
      [[1, 0, 3, 2, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6],
        [0, 1, 2, 3, 6, 7, 4, 5], [1, 0, 2, 3, 5, 4, 6, 7], [4, 5, 6, 7, 0, 1, 2, 3]].getD k [] := by
  decide +kernel

theorem pPlusGens_list : ∀ k < 6, ∀ j : Fin 8, ((pPlusGens.getD k 1).symm j : ℕ) =
    ([[1, 0, 3, 2, 4, 5, 6, 7], [2, 3, 0, 1, 4, 5, 6, 7], [0, 1, 2, 3, 5, 4, 7, 6],
        [0, 1, 2, 3, 6, 7, 4, 5], [1, 0, 2, 3, 5, 4, 6, 7], [4, 5, 6, 7, 0, 1, 2, 3]].getD k
          []).idxOf (j : ℕ) := by
  decide +kernel

theorem frameDecode_even : ∀ k < 7, framePop (1 + 2 ^ (k + 1)) % 2 = 0 ∧ 1 + 2 ^ (k + 1) < 256 := by
  decide +kernel

theorem rep_gen {k : ℕ} (hk : k < 13) : Rep 240 tPlusGensArr[k]! (Φ (e32 GC k)) := by
  have hok := (gens_facts.1 k hk).1
  rcases Nat.lt_or_ge k 7 with h7 | h7
  · rw [tPlusGensArr_sign' h7, ← signArrsL_get (frameDecode_even k h7).2]
    have h := spC_sign hSP (frameDecode_even k h7).2 (frameDecode_even k h7).1
    rw [← gen_codes.1 k h7] at h
    exact rep_of_eqA' (rep_Φ hok) (eqA_comm' h)
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h7
    have hj : j < 6 := by omega
    obtain ⟨h0, hl⟩ := gen_codes.2 j hj
    rw [tPlusGensArr_perm' hj, permArr_eq_listPermArr _ _ (pPlusGens_list j hj), ← hl]
    exact rep_of_eqA' (rep_Φ hok) (eqA_comm' (spC_perm hSP hok h0))

theorem rho_codes : ∀ k < 25, spMask (e32 RH k) = 0 ∧ codeL (e32 RH k) = rhoLists.getD k [] := by
  decide +kernel

theorem rep_rho {k : ℕ} (hk : k < 25) : Rep 240 rhoArrs[k]! (Φ (e32 RH k)) := by
  have hok := (gens_facts.2.2.2.2 k hk).1
  obtain ⟨h0, hl⟩ := rho_codes k hk
  have e : rhoArrs[k]! = listPermArr (rhoLists.getD k []) := by
    rw [rhoArrs, getElem!_pos _ k (by simpa [rhoLists] using hk)]
    simp only [List.getElem_toArray, List.getElem_map]
    rw [List.getD_eq_getElem _ _ (by simpa [rhoLists] using hk)]
  rw [e, ← hl]
  exact rep_of_eqA' (rep_Φ hok) (eqA_comm' (spC_perm hSP hok h0))

theorem rho_inv {k : ℕ} (hk : k < 25) : (Φ (e32 RH k))⁻¹ = Φ (e32 RHI k) := by
  obtain ⟨h1, h2, h3⟩ := gens_facts.2.2.2.2 k hk
  rw [inv_eq_of_mul_eq_one_right]
  rw [Φ_mul h1 h2, h3, Φ_id]

theorem rep_word : ∀ l : List ℕ, wordOKK DPK l = true →
    Rep 240 (wordArr l) (Φ (wordCodeK DPK l))
  | [], _ => by
    change Rep 240 (idA 240) (Φ spId)
    rw [Φ_id]
    exact rep_idA
  | r :: l, h => by
    change (Nat.blt r 112 && (okC (reflCodeK DPK r) && (okC (wordCodeK DPK l) &&
      wordOKK DPK l))) = true at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hr, h1, h2, h3⟩ := h
    have hR := spC_refl hSP hr
    rw [← dpk] at hR
    have hR' : Rep 240 (reflArr r) (Φ (reflCodeK DPK r)) := rep_of_eqA' (rep_Φ h1) hR
    have h := rep_compA hR' (rep_word l h3)
    rw [Φ_mul h1 h2] at h
    exact h

theorem words_spec {W : ℕ → List ℕ} {n C : ℕ} (h : wordsK DPK W n C = true) {k : ℕ} (hk : k < n) :
    Rep 240 (wordArr (W k)) (Φ (e32 C k)) := by
  have h' := allN_spec h k hk
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h'
  rw [← h'.2]
  exact rep_word _ h'.1

theorem bIf_true_iff (c t : Bool) : Bool.rec (motive := fun _ => Bool) true t c = true ↔
    (c = true → t = true) := by
  cases c <;> simp

theorem bIf_true_left_iff (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = true ↔
    (c = false → e = true) := by
  cases c <;> simp

theorem notB'_iff (b : Bool) : notB' b = true ↔ b = false := by cases b <;> decide


structure AtFacts (b : Bool) (x : ℕ) : Prop where
  sqz : b = true → Nat.beq (spMul x x) negC = false
  fg : b = true → Nat.beq (spMul x x) spId = true → fgK x = true
  w8 : Nat.beq (spMul x x) spId = true → Nat.beq x spId = false → w8K RH RHI x = true
  cent : (allN 13 (fun k => commK' x (e32 GC k)) && commK' x s0C) = true →
    Nat.beq x spId = false → Nat.beq x negC = true
  centPlus : b = false → allN 13 (fun k => commK' x (e32 GC k)) = true →
    Nat.beq x spId = false → Nat.beq x negC = true

theorem atFacts {b : Bool} {x : ℕ} (h : factAtK GC RH RHI b x = true) : AtFacts b x := by
  simp only [factAtK, strictB_eq', bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h4, h5, h6, h7, h8⟩ := h
  have w8 : Nat.beq (spMul x x) spId = true → Nat.beq x spId = false → w8K RH RHI x = true := by
    intro ht hx
    simp only [ht, hx] at h6
    exact h6
  have cent : (allN 13 (fun k => commK' x (e32 GC k)) && commK' x s0C) = true →
      Nat.beq x spId = false → Nat.beq x negC = true := by
    intro hc hx
    simp only [hc, hx] at h7
    exact h7
  cases b
  · simp only at h8
    refine ⟨fun hb => absurd hb Bool.false_ne_true,
      fun hb => absurd hb Bool.false_ne_true, w8, cent, fun _ hc hx => ?_⟩
    simp only [hc, hx] at h8
    exact h8
  · simp only at h4 h5
    refine ⟨fun _ => (notB'_iff _).1 h4, fun _ ht => ?_, w8, cent,
      fun hb => Bool.noConfusion hb⟩
    simp only [ht] at h5
    exact h5

theorem facts_at {i : ℕ} (hi : i < 8192) : okC (spMul (tcK PP i) s0C) = true ∧
    AtFacts false (tcK PP i) ∧ AtFacts true (spMul (tcK PP i) s0C) := by
  have h := range_all kF i hi
  simp only [factsAt, strictB_eq', bAnd_eq, Bool.and_eq_true] at h
  exact ⟨okC_mul (okTC hi) gens_facts.2.1, atFacts h.1, atFacts h.2⟩

@[expose] noncomputable def tcB (i : ℕ) (b : Bool) : ℕ := if b then spMul (tcK PP i) s0C else tcK PP i

theorem rep_tEltB {i : ℕ} (hi : i < 8192) (b : Bool) :
    okC (tcB i b) = true ∧ Rep 240 (tElt tPlusCert i b) (Φ (tcB i b)) ∧ AtFacts b (tcB i b) := by
  cases b
  · have e : tcB i false = tcK PP i := rfl
    rw [e]
    exact ⟨okTC hi, rep_tElt hi, (facts_at hi).2.1⟩
  · have e : tcB i true = spMul (tcK PP i) s0C := rfl
    rw [e]
    exact ⟨(facts_at hi).1, rep_tElt_true hi, (facts_at hi).2.2⟩

theorem beq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

theorem ne_of_beq_false {a b : ℕ} (h : Nat.beq a b = false) : a ≠ b := fun e => by
  rw [e, Nat.beq_refl] at h
  exact absurd h (by decide)

theorem sq_rep {x : ℕ} (hx : okC x = true) {t : Array ℕ} (ht : Rep 240 t (Φ x)) :
    Rep 240 (compA 240 t t) (Φ (spMul x x)) := by
  have h := rep_compA ht ht
  rwa [Φ_mul hx hx] at h

theorem comm_code {x g : ℕ} (hx : okC x = true) (hg : okC g = true) (h1 : okC (spMul x g) = true)
    (h2 : okC (spMul g x) = true) {t a : Array ℕ} (ht : Rep 240 t (Φ x)) (ha : Rep 240 a (Φ g))
    (hc : commA' t a = true) : commK' x g = true := by
  have e := (eqA_iff (rep_compA ht ha) (rep_compA ha ht)).1 hc
  rw [Φ_mul hx hg, Φ_mul hg hx] at e
  unfold commK'
  rw [Φ_inj h1 h2 e]
  exact Nat.beq_refl _

theorem pairMask_mem : ∀ a < 8, ∀ b < a, 2 ^ a + 2 ^ b ∈ pairMasks ∧ 2 ^ a + 2 ^ b < 256 ∧
    framePop (2 ^ a + 2 ^ b) % 2 = 0 := by
  decide +kernel

theorem pairSign_ok : ∀ a < 8, ∀ b < a, okC ((2 ^ a + 2 ^ b) * 2 ^ 24 + spId) = true := by
  decide +kernel

theorem fg_of {x : ℕ} (hx : okC x = true) {t : Array ℕ} (ht : Rep 240 t (Φ x))
    (h : fgK x = true) : fgOK signArrs t = true := by
  obtain ⟨a, ha, ha'⟩ := not_allN h
  obtain ⟨b, hb, hb'⟩ := not_allN ((notB'_iff _).2 ha')
  rw [strictB_eq', strictB_eq', strictB_eq', notB'_eq, Bool.not_eq_false'] at hb'
  obtain ⟨hc1, hb'⟩ := (bAnd_iff _ _).1 hb'
  obtain ⟨hc2, hc3⟩ := (bAnd_iff _ _).1 hb'
  replace hc1 := ne_of_beq_false ((notB'_iff _).1 hc1)
  replace hc2 := ne_of_beq_false ((notB'_iff _).1 hc2)
  replace hc3 := Nat.eq_of_beq_eq_true hc3
  obtain ⟨hm, hm256, hme⟩ := pairMask_mem a ha b hb
  have es : Nat.add (Nat.shiftLeft (Nat.add (Nat.shiftLeft 1 a) (Nat.shiftLeft 1 b)) 24) spId =
      (2 ^ a + 2 ^ b) * 2 ^ 24 + spId := by
    change ((1 <<< a) + (1 <<< b)) <<< 24 + spId = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft, Nat.shiftLeft_eq]
  rw [es] at hc1 hc2 hc3
  have hs : okC ((2 ^ a + 2 ^ b) * 2 ^ 24 + spId) = true := pairSign_ok a ha b hb
  have hu := okC_mul hs hx
  have hc := okC_mul hu hu
  have hS : Rep 240 signArrs[2 ^ a + 2 ^ b]! (Φ ((2 ^ a + 2 ^ b) * 2 ^ 24 + spId)) :=
    rep_of_eqA' (rep_Φ hs) (eqA_comm' (spC_sign hSP hm256 hme))
  rw [fgOK, List.any_eq_true]
  refine ⟨_, hm, ?_⟩
  have hU : Rep 240 (compA 240 signArrs[2 ^ a + 2 ^ b]! t)
      (Φ (spMul ((2 ^ a + 2 ^ b) * 2 ^ 24 + spId) x)) := by
    have := rep_compA hS ht
    rwa [Φ_mul hs hx] at this
  have hC := sq_rep hu hU
  have hCC := sq_rep hc hC
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Bool.eq_false_iff.2 fun e => hc1 ((eqId hc hC).1 e)
  · exact Bool.eq_false_iff.2 fun e => hc2 ((eqNeg hc hC).1 e)
  · rw [isId_iff' hCC, hc3, Φ_id]

theorem eqA_entries {x y : Array ℕ} (h : eqA 240 x y = true) : ∀ i < 240, x[i]! = y[i]! := by
  intro i hi
  have := allLt_spec h hi
  rwa [beq_iff_eq] at this

theorem keyPts_getD_lt (i : ℕ) : keyPts.getD i 0 < 240 := by
  rcases Nat.lt_or_ge i 8 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simpa [keyPts] using h)]
    norm_num

theorem memE1_congr {FA : Array (Array ℕ)} {x y : Array ℕ} (h : eqA 240 x y = true) :
    memE1 FA x = memE1 FA y := by
  have hxy := eqA_entries h
  have hm : frameMaskOf x = frameMaskOf y := by
    unfold frameMaskOf
    congr 2
    apply List.filter_congr
    intro i _
    rw [hxy _ (keyPts_getD_lt i)]
  unfold memE1
  rw [hm, Bool.eq_iff_iff, eqA, eqA, allLt_iff, allLt_iff]
  constructor
  · intro hh i hi
    rw [← hxy i hi]
    exact hh i hi
  · intro hh i hi
    rw [hxy i hi]
    exact hh i hi

theorem w8_of {x : ℕ} (hx : okC x = true) {t : Array ℕ} (ht : Rep 240 t (Φ x))
    (h : w8K RH RHI x = true) : w8OK frameArrs rhoArrs t = true := by
  obtain ⟨k, hk, hk'⟩ := not_allN h
  simp only [strictB_eq', notB'_eq, Bool.not_eq_false'] at hk'
  have hf := hk'
  obtain ⟨hr1, hr2, -⟩ := gens_facts.2.2.2.2 k hk
  have hu := okC_mul hr1 hx
  have hv := okC_mul hu hr2
  rw [w8OK, List.any_eq_true]
  refine ⟨k, List.mem_range.2 hk, ?_⟩
  have hR := rep_rho hk
  have hRi : Rep 240 (invCand 240 rhoArrs[k]!) (Φ (e32 RHI k)) := by
    rw [← rho_inv hk]
    exact rep_invCand' hR
  have hc : Rep 240 (conjA' rhoArrs[k]! t) (Φ (spMul (spMul (e32 RH k) x) (e32 RHI k))) := by
    have := rep_compA (rep_compA hR ht) hRi
    rwa [Φ_mul hr1 hx, Φ_mul hu hr2] at this
  rw [memE1_congr ((eqA_iff hc (rep_Φ hv)).2 rfl)]
  change memE1L rootList keyPts (frameArrsL rootList) (spArrC rootList _) = true
  rw [spC_memE1 hSP hv]
  exact hf

theorem tList_facts : TListFacts := by
  have hId := gens_facts.2.2.2.1
  have hS0 := gens_facts.2.1
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, ?_, fun k hk => ?_, fun i hi hpos => ?_,
    fun i hi k hk => ?_, fun m hm he => ?_, fun k hk => ?_, fun i hi => ?_, fun i hi hsq => ?_,
    fun i hi b _ hsq => ?_, fun i hi b _ hc => ?_, fun i hi hc => ?_⟩
  · rw [tElt_eq hi]
    exact spC_valid hSP (okTC hi)
  · refine Bool.eq_false_iff.2 fun e => hij (tcK_inj hi hj ?_)
    exact Φ_inj (okTC hi) (okTC hj) ((eqA_iff (rep_tElt hi) (rep_tElt hj)).1 e)
  · have h0 : tcK PP 0 = spId := by decide +kernel
    exact (eqId (okTC (by norm_num)) (rep_tElt (by norm_num))).2 h0
  · obtain ⟨hg, hgg⟩ := gens_facts.1 k hk
    refine ⟨isInvA_of_rep (rep_gen hk), ?_⟩
    rw [isId_iff' (rep_compA (rep_gen hk) (rep_gen hk)), Φ_mul hg hg, hgg, Φ_id]
  · obtain ⟨k, hk, hj, he⟩ := tree_facts hi hpos
    refine ⟨k, hk, _, hj, ?_⟩
    have h := rep_compA (rep_gen hk) (rep_tElt (hj.trans hi))
    rw [Φ_mul (gens_facts.1 k hk).1 (okTC (hj.trans hi)), he] at h
    exact (eqA_iff (rep_tElt hi) h).2 rfl
  · obtain ⟨hj, he⟩ := (closed_facts hi).2 k hk
    refine ⟨_, hj, ?_⟩
    have h := rep_compA (rep_gen hk) (rep_tElt hi)
    rw [Φ_mul (gens_facts.1 k hk).1 (okTC hi), ← he] at h
    exact (eqA_iff h (rep_tElt hj)).2 rfl
  · have hm2 : m / 2 < 8192 := by omega
    refine ⟨m / 2, hm2, ?_⟩
    have ec : tcK PP (m / 2) = m * 2 ^ 24 + spId := by
      have hs : ∀ m < 256, framePop m % 2 = 0 → tcK PP (m / 2) = m * 2 ^ 24 + spId := by
        decide +kernel
      exact hs m hm he
    have hS : Rep 240 signArrs[m]! (Φ (m * 2 ^ 24 + spId)) := by
      rw [← ec]
      exact rep_of_eqA' (rep_Φ (okTC hm2)) (eqA_comm' (by rw [ec]; exact spC_sign hSP hm he))
    have hT := rep_tElt hm2
    rw [ec] at hT
    exact (eqA_iff hS hT).2 rfl
  · obtain ⟨j, hj⟩ := (⟨_, rfl⟩ : ∃ j, j = pg 16 65535 S0J k)
    have h := allN_spec kS0 k hk
    simp only [strictB_eq', bAnd_eq, Bool.and_eq_true, Nat.blt_eq,
      Nat.beq_eq] at h
    obtain ⟨hgs, hjl, he⟩ := h
    refine ⟨_, hjl, ?_⟩
    have h1 := rep_compA (rep_compA rep_s0Arr' (rep_gen hk)) rep_s0Arr'
    rw [mul_assoc, Φ_mul (gens_facts.1 k hk).1 hS0, Φ_mul hS0 hgs, ← he] at h1
    exact (eqA_iff h1 (rep_tElt hjl)).2 rfl
  · obtain ⟨hok, hrep, hf⟩ := rep_tEltB hi true
    refine Bool.eq_false_iff.2 fun e => ?_
    have := (eqNeg (okC_mul hok hok) (sq_rep hok hrep)).1 e
    have h2 := hf.sqz rfl
    rw [this] at h2
    exact absurd h2 (by decide +kernel)
  · obtain ⟨hok, hrep, hf⟩ := rep_tEltB hi true
    have h2 : spMul (tcB i true) (tcB i true) = spId :=
      (eqId (okC_mul hok hok) (sq_rep hok hrep)).1 hsq
    exact fg_of hok hrep (hf.fg rfl (by rw [h2]; exact Nat.beq_refl _))
  · obtain ⟨hok, hrep, hf⟩ := rep_tEltB hi b
    have h2 : spMul (tcB i b) (tcB i b) = spId := (eqId (okC_mul hok hok) (sq_rep hok hrep)).1 hsq
    by_cases hx : tcB i b = spId
    · exact Or.inl ((eqId hok hrep).2 hx)
    · exact Or.inr (w8_of hok hrep (hf.w8 (by rw [h2]; exact Nat.beq_refl _) (beq_false hx)))
  · obtain ⟨hok, hrep, hf⟩ := rep_tEltB hi b
    have hcg : allN 13 (fun k => commK' (tcB i b) (e32 GC k)) = true := allN_of_forall fun k hk =>
      comm_code hok (gens_facts.1 k hk).1 (okC_mul hok (gens_facts.1 k hk).1)
        (okC_mul (gens_facts.1 k hk).1 hok) hrep (rep_gen hk) (allLt_spec hc.1 hk)
    have hcs : commK' (tcB i b) s0C = true :=
      comm_code hok hS0 (okC_mul hok hS0) (okC_mul hS0 hok) hrep rep_s0Arr' hc.2
    by_cases hx : tcB i b = spId
    · exact Or.inl ((eqId hok hrep).2 hx)
    · refine Or.inr ((eqNeg hok hrep).2 (Nat.eq_of_beq_eq_true ?_))
      exact hf.cent (by rw [hcg, hcs]; rfl) (beq_false hx)
  · obtain ⟨hok, hrep, hf⟩ := rep_tEltB hi false
    have hcg : allN 13 (fun k => commK' (tcB i false) (e32 GC k)) = true :=
      allN_of_forall fun k hk => comm_code hok (gens_facts.1 k hk).1
        (okC_mul hok (gens_facts.1 k hk).1) (okC_mul (gens_facts.1 k hk).1 hok) hrep (rep_gen hk)
        (allLt_spec hc hk)
    by_cases hx : tcB i false = spId
    · exact Or.inl ((eqId hok hrep).2 hx)
    · exact Or.inr ((eqNeg hok hrep).2 (Nat.eq_of_beq_eq_true (hf.centPlus rfl hcg
        (beq_false hx))))

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3186 : TListFacts
    ∧ (rhoWordCheck = true)
    ∧ (tGenCheck = true) := by
  refine ⟨tList_facts, ?_, ?_⟩
  · rw [rhoWordCheck, allLt_iff]
    intro k hk
    rw [Bool.and_eq_true]
    exact ⟨isInvA_of_rep (rep_rho hk), (eqA_iff (rep_rho hk) (words_spec kRW hk)).2 rfl⟩
  · rw [tGenCheck, allLt_iff]
    intro k hk
    exact (eqA_iff (rep_gen hk) (words_spec kTG hk)).2 rfl

end CertificateChecks.KernelLC.W3186

end
