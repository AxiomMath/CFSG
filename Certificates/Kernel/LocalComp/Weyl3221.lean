module

public import Certificates.Kernel.LocalComp.Weyl3221K
public import Certificates.Kernel.LocalComp.Weyl3222
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 400000

namespace CertificateChecks.KernelLC.W3221

open CFSG.KC.Enum CFSG.KS CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelLC
open CFSG.RankThree.Native (rep_of_eqA permOfArr_eq_of_rep validA)
open CertificateChecks.KernelLC.W3186

attribute [local irreducible] okC spMul UC UG UGI UPP ULP FX LR Q1C Q0C pCodes pMulT pInvT

theorem e24_eq (P k : ℕ) : e24 P k = P / 2 ^ (24 * k) % 2 ^ 24 := by
  change (P >>> (24 * k)) &&& (2 ^ 24 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pg7 (X k : ℕ) : pg 7 127 X k = X / 2 ^ (7 * k) % 128 := by
  change (X >>> (7 * k)) &&& (2 ^ 7 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pListArr_get (i : ℕ) {j : ℕ} (hj : j < 8) : (pListArr i)[j]! = spAt (e24 pCodes i) j := by
  rw [pListArr, getElem!_ofFn_nat _ hj, spAt_eq, e24_eq]

theorem pMul_eq (i j : ℕ) : pMul i j = pMulK pMulT i j := by
  rw [pMul, pMulK, pg7]
  rfl

theorem pInv_eq (i : ℕ) : pInv i = pInvK pInvT i := by
  rw [pInv, pInvK, pg7]

theorem pPar_eq (i : ℕ) : pPar i = pg 7 127 pParT i := by
  rw [pPar, pg7]

theorem pLab_eq (i : ℕ) : pLab i = pg 3 7 pLabT i := by
  rw [pLab, pg3]

theorem allN_eq_all (n : ℕ) (f : ℕ → Bool) : allN n f = (List.range n).all f := by
  rw [Bool.eq_iff_iff, allN_iff, List.all_eq_true]
  exact ⟨fun h i hi => h i (List.mem_range.1 hi), fun h i hi => h i (List.mem_range.2 hi)⟩

theorem eqA8_iff {t u : Array ℕ} : eqA 8 t u = true ↔ ∀ j < 8, t[j]! = u[j]! := by
  rw [eqA, allLt_iff]
  simp only [beq_iff_eq]

theorem spId_at : ∀ x < 8, spAt spId x = x := by decide +kernel

theorem spMask_small {c : ℕ} (hc : c < 2 ^ 24) : spMask c = 0 := by
  rw [spMask_eq, Nat.div_eq_of_lt hc]

theorem code24_eq {a b : ℕ} (ha : a < 2 ^ 24) (hb : b < 2 ^ 24) (h : ∀ j < 8, spAt a j = spAt b j) :
    a = b := by
  refine eq_of_spMask_codeL (ha.trans (by norm_num)) (hb.trans (by norm_num))
    (by rw [spMask_small ha, spMask_small hb]) ?_
  rw [codeL, codeL]
  exact List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

theorem rep8_of_perm {t : Array ℕ} {c : ℕ} (ht : ∀ j < 8, t[j]! = spAt c j)
    (hc : permOKK c = true) : ∃ σ : Equiv.Perm (Fin 8), Rep 8 t σ := by
  let f : Fin 8 → Fin 8 := fun x => ⟨spAt c x, spAt_lt c x⟩
  have hf : Function.Surjective f := fun y => by
    have hy := permOKK_spec hc y y.2
    rw [codeL, List.mem_map] at hy
    obtain ⟨x, hx, e⟩ := hy
    exact ⟨⟨x, List.mem_range.1 hx⟩, Fin.ext e⟩
  exact ⟨Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩, fun x => ht x x.2⟩

theorem isInvA8 {t : Array ℕ} {X : Equiv.Perm (Fin 8)} (ht : Rep 8 t X) :
    isInvA 8 t (invCand 8 t) = true := by
  have hr := rep_invCand' ht
  rw [isInvA, allLt_iff]
  intro i hi
  have h1 := ht ⟨i, hi⟩
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨by rw [h1]; exact (X ⟨i, hi⟩).2, ?_⟩
  rw [h1, hr (X ⟨i, hi⟩)]
  simp

theorem not_beq_true {a b : ℕ} (h : notB' (Nat.beq a b) = true) : a ≠ b := by
  rw [notB'_eq, Bool.not_eq_true'] at h
  exact W3186.ne_of_beq_false h

theorem all_congr' {l : List ℕ} {f g : ℕ → Bool} (h : ∀ i ∈ l, f i = g i) : l.all f = l.all g := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun h' i hi => h i hi ▸ h' i hi, fun h' i hi => (h i hi).symm ▸ h' i hi⟩

theorem beq_nat (a b : ℕ) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem nIf_eq' (c : Bool) (t e : ℕ) :
    Bool.rec (motive := fun _ => ℕ) e t c = if c = true then t else e := by cases c <;> rfl

theorem getD_mem' {l : List ℕ} {k : ℕ} (hk : k < l.length) : l.getD k 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

theorem tree_ne {i : ℕ} (hi : 0 < i) : Nat.beq i 0 = false := by
  rcases i with _ | i
  · omega
  · rfl

theorem p_k : (∀ i < 128, permOKK (e24 pCodes i) = true) ∧
    (∀ i < 128, ∀ j < i, e24 pCodes i ≠ e24 pCodes j) ∧ e24 pCodes 0 = spId ∧
    (∀ i < 128, ∀ j < 128, spMul (e24 pCodes i) (e24 pCodes j) = e24 pCodes (pMul i j)) ∧
    (∀ i < 128, spMul (e24 pCodes i) (e24 pCodes (pInv i)) = spId) ∧
    ∀ i < 128, 0 < i → pPar i < i ∧ pLab i < 7 ∧ pMul (pLab i + 1) (pPar i) = i := by
  have h := kP
  unfold pListK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨allN_spec h1, fun i hi j hj => not_beq_true (allN_spec (allN_spec h2 i hi) j hj),
    Nat.eq_of_beq_eq_true h3, fun i hi j hj => ?_, fun i hi => ?_, fun i hi hpos => ?_⟩
  · rw [pMul_eq]
    exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec h4 i hi) j hj)
  · rw [pInv_eq]
    exact Nat.eq_of_beq_eq_true (allN_spec h5 i hi)
  · have h := allN_spec h6 i hi
    simp only [tree_ne hpos, strictB_eq', Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hp, hl, he⟩ := h
    rw [pPar_eq, pLab_eq, pMul_eq]
    exact ⟨hp, hl, Nat.eq_of_beq_eq_true he⟩

theorem p_gens : ∀ k < 7, ∀ x : Fin 8,
    (((Equiv.swap 0 1 :: pPlusGens).getD k 1) x : ℕ) = spAt (e24 pCodes (k + 1)) x := by
  decide +kernel

theorem p_list_ok : PListFacts := by
  obtain ⟨hperm, hdist, hid, hmul, hinv, htree⟩ := p_k
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_, ?_, fun i hi j hj => ?_, fun i hi => ?_,
    fun k hk => ?_, htree⟩
  · obtain ⟨σ, hσ⟩ := rep8_of_perm (fun j hj => pListArr_get i hj) (hperm i hi)
    exact isInvA8 hσ
  · by_contra h
    rw [Bool.not_eq_false, eqA8_iff] at h
    have e := code24_eq (a := e24 pCodes i) (b := e24 pCodes j) (e24_lt _ _) (e24_lt _ _)
      fun x hx => by
      rw [← pListArr_get i hx, ← pListArr_get j hx]
      exact h x hx
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact hdist j hj i hlt e.symm
    · exact hdist i hi j hlt e
  · rw [eqA8_iff]
    intro x hx
    rw [pListArr_get 0 hx, idA_get hx, hid, spId_at x hx]
  · rw [eqA8_iff]
    intro x hx
    rw [compA_get hx, pListArr_get j hx, pListArr_get i (spAt_lt _ _), pListArr_get _ hx,
      ← hmul i hi j hj, spAt_mul _ _ hx]
  · rw [eqA8_iff]
    intro x hx
    rw [compA_get hx, pListArr_get _ hx, pListArr_get i (spAt_lt _ _), idA_get hx,
      ← spAt_mul _ _ hx, hinv i hi, spId_at x hx]
  · rw [eqA8_iff]
    intro x hx
    rw [perm8Arr, getElem!_ofFn_nat _ hx, pListArr_get _ hx]
    exact p_gens k hk ⟨x, hx⟩

theorem nthK_eq : ∀ (l : List ℕ) (k : ℕ), nthK l k = l.getD k 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => nthK_eq l k

theorem wordIdxK_eq (gi : List ℕ) : ∀ w : List ℕ, wordIdxK pMulT gi w = wordIdx gi w
  | [] => rfl
  | k :: w => by
    change pMulK pMulT (nthK gi k) (wordIdxK pMulT gi w) = pMul (gi.getD k 0) (wordIdx gi w)
    rw [wordIdxK_eq gi w, nthK_eq, pMul_eq]

theorem wordsHitK_spec {gi : List ℕ} {i : ℕ} :
    ∀ {W : List (List ℕ)}, wordsHitK pMulT gi W i = true → ∃ w ∈ W, wordIdx gi w = i
  | [], h => absurd h Bool.false_ne_true
  | w :: W, h => by
    change Bool.rec (motive := fun _ => Bool) (wordsHitK pMulT gi W i) true
      (Nat.beq (wordIdxK pMulT gi w) i) = true at h
    cases hb : Nat.beq (wordIdxK pMulT gi w) i
    · rw [hb] at h
      obtain ⟨w', hw', e⟩ := wordsHitK_spec h
      exact ⟨w', List.mem_cons_of_mem _ hw', e⟩
    · exact ⟨w, List.mem_cons_self .., (wordIdxK_eq gi w).symm.trans (Nat.eq_of_beq_eq_true hb)⟩

theorem gis_spec {M : ℕ} : ∀ {gi : List ℕ}, List.rec (motive := fun _ => Bool) true
    (fun g _ ih => bAnd(Nat.blt g (nat_lit 128), bAnd(bitK M g, ih))) gi = true →
    ∀ g ∈ gi, g < 128 ∧ M.testBit g = true
  | [], _ => fun _ hg => absurd hg List.not_mem_nil
  | g :: gi, h => by
    change bAnd(Nat.blt g (nat_lit 128), bAnd(bitK M g, List.rec (motive := fun _ => Bool) true
      (fun g _ ih => bAnd(Nat.blt g (nat_lit 128), bAnd(bitK M g, ih))) gi)) = true at h
    obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
    obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
    intro g' hg'
    rcases List.mem_cons.1 hg' with rfl | hg'
    · exact ⟨by simpa using h1, by rwa [bitK_eq] at h2⟩
    · exact gis_spec h3 g' hg'

theorem sub_ok {gs : List (Equiv.Perm (Fin 8))} {gi : List ℕ} {M : ℕ} {W : List (List ℕ)}
    (k : subK pMulT pInvT M gi W = true) (hlen : gi.length = gs.length)
    (hg : ∀ k < gs.length, ∀ x : Fin 8, ((gs.getD k 1) x : ℕ) = spAt (e24 pCodes (gi.getD k 0)) x) :
    SubListFacts gs gi M W := by
  unfold subK at k
  obtain ⟨h0, k⟩ := (bAnd_iff _ _).1 k
  obtain ⟨hlt, k⟩ := (bAnd_iff _ _).1 k
  obtain ⟨hgi, k⟩ := (bAnd_iff _ _).1 k
  obtain ⟨hmul, k⟩ := (bAnd_iff _ _).1 k
  obtain ⟨hinv, hw⟩ := (bAnd_iff _ _).1 k
  have hgi' := gis_spec hgi
  refine ⟨hlen, fun k hk => ?_, fun k hk => hgi' _ (getD_mem' hk), by rwa [← bitK_eq],
    by simpa using hlt, fun i hi j hj hmi hmj => ?_, fun i hi hmi => ?_, fun i hi hmi => ?_⟩
  · rw [eqA8_iff]
    intro x hx
    rw [perm8Arr, getElem!_ofFn_nat _ hx, pListArr_get _ hx]
    exact hg k hk ⟨x, hx⟩
  · have h := (bIf_true_iff _ _).1 (allN_spec hmul i hi) (by rwa [bitK_eq])
    have h := (bIf_true_iff _ _).1 (allN_spec h j hj) (by rwa [bitK_eq])
    rwa [bitK_eq, ← pMul_eq] at h
  · have h := (bIf_true_iff _ _).1 (allN_spec hinv i hi) (by rwa [bitK_eq])
    rwa [bitK_eq, ← pInv_eq] at h
  · exact wordsHitK_spec ((bIf_true_iff _ _).1 (allN_spec hw i hi) (by rwa [bitK_eq]))

theorem sub_gens_plus : ∀ k < pPlusGens.length, ∀ x : Fin 8,
    ((pPlusGens.getD k 1) x : ℕ) = spAt (e24 pCodes (pPlusIdx.getD k 0)) x := by
  decide +kernel

theorem sub_gens_q1 : ∀ k < q1Gens.length, ∀ x : Fin 8,
    ((q1Gens.getD k 1) x : ℕ) = spAt (e24 pCodes (q1Idx.getD k 0)) x := by
  decide +kernel

theorem sub_gens_q0 : ∀ k < q0Gens.length, ∀ x : Fin 8,
    ((q0Gens.getD k 1) x : ℕ) = spAt (e24 pCodes (q0Idx.getD k 0)) x := by
  decide +kernel

theorem validExt_eq (m x : ℕ) : validExt m x = validK pMulT m x := by
  rw [validExt, validK, bAnd_eq, bAnd_eq, notB'_eq, bitK_eq, bitK_eq, ← pMul_eq, allN_eq_all,
    Bool.and_assoc]
  refine congrArg (fun b => (!m.testBit x && (m.testBit (pMul x x) && b)))
    (all_congr' fun i _ => ?_)
  rw [bIf_eq, bitK_eq, ← pMul_eq, ← pMul_eq, beq_nat]
  cases m.testBit i <;> rfl

theorem bitsOf_eq (p : ℕ → Bool) : ∀ n : ℕ, Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun n ih => Nat.lor ih (nIf(p n, Nat.shiftLeft (nat_lit 1) n, nat_lit 0))) n = bitsOf p n
  | 0 => rfl
  | n + 1 => by
    change Nat.lor (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun n ih => Nat.lor ih (nIf(p n, Nat.shiftLeft (nat_lit 1) n, nat_lit 0))) n)
        (nIf(p n, Nat.shiftLeft (nat_lit 1) n, nat_lit 0)) =
      bitsOf p n ||| (if p n then 2 ^ n else 0)
    rw [bitsOf_eq p n]
    cases p n
    · rfl
    · change bitsOf p n ||| (1 <<< n) = _
      rw [Nat.shiftLeft_eq, one_mul]
      rfl

theorem extMask_eq (m x : ℕ) : extMask m x = extK pMulT pInvT m x := by
  have e := bitsOf_eq (fun n => bitK m (pMulK pMulT (pInv x) n)) 128
  rw [extK, strictN_eq', extMask, ← pInv_eq]
  refine congrArg (m ||| ·) (Eq.trans ?_ e.symm)
  congr 1
  funext j
  rw [bitK_eq, pMul_eq]

theorem inListK_spec {e : ℕ} : ∀ {L : List ℕ}, inListK L e = true → e ∈ L
  | [], h => absurd h Bool.false_ne_true
  | a :: L, h => by
    change Bool.rec (motive := fun _ => Bool) (inListK L e) true (Nat.beq a e) = true at h
    cases hb : Nat.beq a e
    · rw [hb] at h
      exact List.mem_cons_of_mem _ (inListK_spec h)
    · rw [← Nat.eq_of_beq_eq_true hb]
      exact List.mem_cons_self ..

theorem subMask_eq (m M : ℕ) : subMask m M = subMaskK m M := by
  rw [subMask, subMaskK, allN_eq_all]
  refine all_congr' fun i _ => ?_
  rw [bIf_eq, bitK_eq, bitK_eq]
  cases m.testBit i <;> rfl

theorem fixAK_eq (i n : ℕ) : fixAK (e24 pCodes i) n = fixA (pListArr i) n := by
  rw [fixAK, fixA, allN_eq_all]
  refine all_congr' fun j hj => ?_
  rw [pListArr_get i (List.mem_range.1 hj), bIf_eq, bitK_eq, bitK_eq, notB'_eq]
  cases n.testBit (spAt (e24 pCodes i) j) <;> cases n.testBit j <;> rfl

theorem fx_k {i n : ℕ} (hi : i < 128) (hn : n < 256) :
    (fxAt FX i).testBit n = fixA (pListArr i) n := by
  have h := allN_spec kFX i hi
  simp only [strictB_eq'] at h
  have h' := allN_spec h n hn
  rw [bIf_eq, bitK_eq, fixAK_eq, notB'_eq] at h'
  cases hb : (fxAt FX i).testBit n <;> rw [hb] at h' <;> simp_all

theorem foldAnd_testBit (m : ℕ) {n : ℕ} (hn : n < 256) : ∀ N : ℕ,
    (Nat.rec (motive := fun _ => Nat)
      (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1))
      (fun i ih => nIf(bitK m i, Nat.land ih (fxAt FX i), ih)) N).testBit n =
      (List.range N).all fun i => !m.testBit i || (fxAt FX i).testBit n
  | 0 => by
    change (2 ^ 256 - 1).testBit n = true
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact hn
  | N + 1 => by
    rw [List.range_succ, List.all_append, ← foldAnd_testBit m hn N]
    change (nIf(bitK m N, Nat.land _ (fxAt FX N), _)).testBit n = _
    rw [bitK_eq]
    cases hb : m.testBit N <;> simp [hb, Nat.land_eq, Nat.testBit_and]

theorem length_filter_range (p : ℕ → Bool) : ∀ N : ℕ,
    ((List.range N).filter p).length = ∑ n ∈ Finset.range N, if p n then 1 else 0
  | 0 => rfl
  | N + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, length_filter_range p N,
      Finset.sum_range_succ]
    cases h : p N <;> simp [h]

theorem fixEven_eq (m : ℕ) : fixEven m = fixK FX m := by
  rw [fixK, strictN_eq', sumN_eq, fixEven, length_filter_range]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' := Finset.mem_range.1 hn
  rw [nIf_eq', bAnd_eq, bitK_eq, foldAnd_testBit m hn' (nat_lit 128)]
  have hfe : evenB n = (framePop n % 2 == 0) := by
    rw [evenB, pop8_eq, Nat.land_eq, Nat.and_one_is_mod, beq_nat]
  have hall : ((List.range 128).all fun i => !m.testBit i || (fxAt FX i).testBit n) =
      (List.range 128).all fun i => !m.testBit i || fixA (pListArr i) n :=
    all_congr' fun i hi => by rw [fx_k (List.mem_range.1 hi) hn']
  rw [hfe]
  exact congrArg (fun b => if (framePop n % 2 == 0 && b) = true then 1 else 0) hall.symm

theorem layerValOK_of {k m : ℕ} (h : layerValK FX pPlusMask q1Mask q0Mask k m = true) :
    layerValOK k m = true := by
  have e : Nat.shiftLeft (fixK FX m) k = fixEven m * 2 ^ k := by
    rw [← fixEven_eq]
    exact Nat.shiftLeft_eq _ _
  unfold layerValK at h
  rw [strictB_eq', e] at h
  rw [layerValOK, subMask_eq]
  generalize fixEven m * 2 ^ k = v at h ⊢
  generalize subMaskK m pPlusMask = s at h ⊢
  simp only [bIf_eq, Nat.ble_eq, Nat.beq_eq] at h
  cases s
  · simp_all
  · simp_all
    omega

theorem layerK_cons (k m : ℕ) (L L' : List ℕ) :
    layerK pMulT pInvT FX pPlusMask q1Mask q0Mask k (m :: L) L' =
      bAnd(allN (nat_lit 128) (fun x => bIf(validK pMulT m x, inListK L' (extK pMulT pInvT m x),
        true)), bAnd(layerValK FX pPlusMask q1Mask q0Mask k m,
          layerK pMulT pInvT FX pPlusMask q1Mask q0Mask k L L')) := rfl

theorem layer_of {k : ℕ} {L' : List ℕ} : ∀ {L : List ℕ},
    layerK pMulT pInvT FX pPlusMask q1Mask q0Mask k L L' = true → ∀ m ∈ L,
      (∀ x < 128, validExt m x = true → extMask m x ∈ L') ∧ layerValOK k m = true
  | [], _ => fun _ hm => absurd hm List.not_mem_nil
  | m :: L, h => by
    rw [layerK_cons, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
    intro m' hm'
    rcases List.mem_cons.1 hm' with rfl | hm'
    · refine ⟨fun x hx hv => ?_, layerValOK_of h.2.1⟩
      have h1 := allN_spec h.1 x hx
      rw [bIf_eq, ← validExt_eq, hv, ← extMask_eq] at h1
      exact inListK_spec (by simpa using h1)
    · exact layer_of h.2.2 m' hm'

theorem layer_ok : LayerFacts := by
  have key : ∀ k < 5, ∀ m ∈ layer k,
      (∀ x < 128, validExt m x = true → extMask m x ∈ layer (k + 1)) ∧ layerValOK k m = true := by
    intro k hk
    interval_cases k
    exacts [layer_of kL0, layer_of kL1, layer_of kL2, layer_of kL3, layer_of kL4]
  exact ⟨fun k hk m hm => (key k hk m hm).1, fun k hk m hm => (key k hk m hm).2⟩

theorem u_codes : ∀ i < 128, spMask (e32 UC i) = uMasks.getD i 0 ∧
    codeL (e32 UC i) = uPerms.getD i [] := by
  decide +kernel

theorem u_k : (∀ i < 128, okC (e32 UC i) = true) ∧ (∀ i < 128, ∀ j < i, e32 UC i ≠ e32 UC j) ∧
    e32 UC 0 = spId ∧
    (∀ k < 4, okC (e32 UG k) = true ∧ okC (e32 UGI k) = true ∧
      spMul (e32 UG k) (e32 UGI k) = spId) ∧
    (∀ i < 128, 0 < i → ∃ l < 4, ∃ p < i, e32 UC i = spMul (e32 UG l) (e32 UC p)) ∧
    (∀ i < 128, ∀ k < 4, inL UC 128 (spMul (e32 UG k) (e32 UC i)) = true ∧
      inL UC 128 (spMul (e32 UGI k) (e32 UC i)) = true) ∧
    (∀ i < 4, ∀ j < 4, commB (e32 UG i) (e32 UG j) = true) ∧
    spMul (e32 UG 1) (e32 UG 1) ≠ spId := by
  have h := kU
  unfold uListK at h
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨allN_spec h1, fun i hi j hj => not_beq_true (allN_spec (allN_spec h2 i hi) j hj),
    Nat.eq_of_beq_eq_true h3, fun k hk => ?_, fun i hi hpos => ?_,
    fun i hi k hk => ?_, fun i hi j hj => allN_spec (allN_spec h7 i hi) j hj, not_beq_true h8⟩
  · have h := allN_spec h4 k hk
    simp only [strictB_eq', Bool.and_eq_true] at h
    exact ⟨h.1, h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩
  · have h := allN_spec h5 i hi
    simp only [tree_ne hpos, strictB_eq', Bool.and_eq_true, Nat.blt_eq] at h
    exact ⟨_, h.2.1, _, h.1, Nat.eq_of_beq_eq_true h.2.2⟩
  · have h := allN_spec (allN_spec h6 i hi) k hk
    simpa only [bAnd_eq, Bool.and_eq_true] using h

theorem inL_spec {x : ℕ} (h : inL UC 128 x = true) : ∃ j < 128, e32 UC j = x := by
  obtain ⟨j, hj, e⟩ := not_allN h
  rw [notB'_eq, Bool.not_eq_false'] at e
  exact ⟨j, hj, Nat.eq_of_beq_eq_true e⟩

theorem okUC {i : ℕ} (hi : i < 128) : okC (e32 UC i) = true := u_k.1 i hi

theorem okUG {k : ℕ} (hk : k < 4) : okC (e32 UG k) = true := (u_k.2.2.2.1 k hk).1

theorem uElt_eq {i : ℕ} (hi : i < 128) : uPrimeCert.pts[i]! = spArrC rootList (e32 UC i) := by
  simp only [uPrimeCert]
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, spArrC, (u_codes i hi).1,
    (u_codes i hi).2, spArr_eq]

theorem rep_uElt {i : ℕ} (hi : i < 128) : Rep 240 uPrimeCert.pts[i]! (Φ (e32 UC i)) := by
  rw [uElt_eq hi]
  exact rep_Φ (okUC hi)

theorem q_codes : (∀ k < 4, spMask (e32 Q1C k) = 0 ∧ ∀ j : Fin 8,
      ((q1Gens.getD k 1).symm j : ℕ) = (codeL (e32 Q1C k)).idxOf (j : ℕ)) ∧
    ∀ k < 3, spMask (e32 Q0C k) = 0 ∧ ∀ j : Fin 8,
      ((q0Gens.getD k 1).symm j : ℕ) = (codeL (e32 Q0C k)).idxOf (j : ℕ) := by
  decide +kernel

theorem okQ : (∀ k < 4, okC (e32 Q1C k) = true) ∧ ∀ k < 3, okC (e32 Q0C k) = true := by
  decide +kernel

theorem rep_q1 {k : ℕ} (hk : k < 4) : Rep 240 (permArr (q1Gens.getD k 1)) (Φ (e32 Q1C k)) := by
  obtain ⟨h0, hl⟩ := q_codes.1 k hk
  rw [permArr_eq_listPermArr _ _ hl]
  exact rep_of_eqA' (rep_Φ (okQ.1 k hk)) (eqA_comm' (spC_perm hSP (okQ.1 k hk) h0))

theorem rep_q0 {k : ℕ} (hk : k < 3) : Rep 240 (permArr (q0Gens.getD k 1)) (Φ (e32 Q0C k)) := by
  obtain ⟨h0, hl⟩ := q_codes.2 k hk
  rw [permArr_eq_listPermArr _ _ hl]
  exact rep_of_eqA' (rep_Φ (okQ.2 k hk)) (eqA_comm' (spC_perm hSP (okQ.2 k hk) h0))

theorem sign_ok : ∀ m ∈ [3, 5, 17, 65, 0, 10, 34, 40, 130, 136, 160, 170],
    m < 256 ∧ framePop m % 2 = 0 ∧ okC (signC m) = true := by
  decide +kernel

theorem rep_sign'' {m : ℕ} (hm : m ∈ [3, 5, 17, 65, 0, 10, 34, 40, 130, 136, 160, 170]) :
    Rep 240 signArrs[m]! (Φ (signC m)) :=
  rep_sign (sign_ok m hm).1 (sign_ok m hm).2.1 (sign_ok m hm).2.2

theorem signArr_vec2 : signArr (vec2 0 1) = signArrs[3]! ∧ signArr (vec2 0 2) = signArrs[5]! ∧
    signArr (vec2 0 4) = signArrs[17]! ∧ signArr (vec2 0 6) = signArrs[65]! := by
  have d3 : frameDecode 3 = vec2 0 1 := by decide
  have d5 : frameDecode 5 = vec2 0 2 := by decide
  have d17 : frameDecode 17 = vec2 0 4 := by decide
  have d65 : frameDecode 65 = vec2 0 6 := by decide
  rw [signArrs_eqL, signArrsL_get (by norm_num), signArrsL_get (by norm_num),
    signArrsL_get (by norm_num), signArrsL_get (by norm_num), d3, d5, d17, d65]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem ug_codes : e32 UG 0 = signC 3 ∧ e32 UG 1 = spMul (signC 5) (e32 Q0C 0) ∧
    e32 UG 2 = spMul (signC 17) (e32 Q0C 1) ∧ e32 UG 3 = spMul (signC 65) (e32 Q0C 2) := by
  decide +kernel

theorem q0Gens_get : q0Gens.getD 0 1 = Equiv.swap 0 1 * Equiv.swap 2 3 ∧
    q0Gens.getD 1 1 = Equiv.swap 0 1 * Equiv.swap 4 5 ∧
    q0Gens.getD 2 1 = Equiv.swap 0 1 * Equiv.swap 6 7 := ⟨rfl, rfl, rfl⟩

theorem rep_ug {m j : ℕ} (hm : m ∈ [3, 5, 17, 65, 0, 10, 34, 40, 130, 136, 160, 170]) (hj : j < 3) :
    Rep 240 (compA 240 signArrs[m]! (permArr (q0Gens.getD j 1)))
      (Φ (spMul (signC m) (e32 Q0C j))) :=
  rep_mul (sign_ok _ hm).2.2 (okQ.2 _ hj) (rep_sign'' hm) (rep_q0 hj)

theorem uPrimeGensArr_get : uPrimeGensArr[0]! = signArr (vec2 0 1) ∧
    uPrimeGensArr[1]! = compA 240 (signArr (vec2 0 2)) (permArr (Equiv.swap 0 1 * Equiv.swap 2 3)) ∧
    uPrimeGensArr[2]! = compA 240 (signArr (vec2 0 4)) (permArr (Equiv.swap 0 1 * Equiv.swap 4 5)) ∧
    uPrimeGensArr[3]! =
      compA 240 (signArr (vec2 0 6)) (permArr (Equiv.swap 0 1 * Equiv.swap 6 7)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [uPrimeGensArr, List.getElem!_toArray,
    List.getElem!_cons_succ, List.getElem!_cons_zero]

theorem rep_uGen {k : ℕ} (hk : k < 4) : Rep 240 uPrimeGensArr[k]! (Φ (e32 UG k)) := by
  obtain ⟨g0, g1, g2, g3⟩ := ug_codes
  obtain ⟨s0, s1, s2, s3⟩ := signArr_vec2
  obtain ⟨u0, u1, u2, u3⟩ := uPrimeGensArr_get
  obtain ⟨q0, q1, q2⟩ := q0Gens_get
  have r1 := rep_ug (m := 5) (j := 0) (by simp) (by norm_num)
  have r2 := rep_ug (m := 17) (j := 1) (by simp) (by norm_num)
  have r3 := rep_ug (m := 65) (j := 2) (by simp) (by norm_num)
  rw [q0] at r1
  rw [q1] at r2
  rw [q2] at r3
  interval_cases k
  · rw [g0, u0, s0]
    exact rep_sign'' (by simp)
  · rw [g1, u1, s1]
    exact r1
  · rw [g2, u2, s2]
    exact r2
  · rw [g3, u3, s3]
    exact r3

theorem rep_uGenInv {k : ℕ} (hk : k < 4) :
    Rep 240 (invCand 240 uPrimeGensArr[k]!) (Φ (e32 UGI k)) := by
  obtain ⟨hg, hgi, he⟩ := u_k.2.2.2.1 k hk
  have h := rep_invCand' (rep_uGen hk)
  rwa [inv_eq_of_mul_eq_one_right (by rw [Φ_mul hg hgi, he, Φ_id])] at h

theorem u_list_ok : UListFacts := by
  obtain ⟨hok, hdist, hid, hgen, htree, hcl, hcomm, hsq⟩ := u_k
  refine ⟨fun i hi => isInvA_of_rep (rep_uElt hi), fun i hi j hj hij => ?_, ?_,
    fun k hk => isInvA_of_rep (rep_uGen hk), fun i hi hpos => ?_, fun i hi k hk => ?_,
    fun i hi k hk => ?_, fun i hi j hj => ?_, ?_⟩
  · rw [eqA_code (hok i hi) (hok j hj) (rep_uElt hi) (rep_uElt hj)]
    rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
    · exact beq_false (hdist j hj i hlt).symm
    · exact beq_false (hdist i hi j hlt)
  · change eqA 240 _ (idA 240) = true
    rw [eqA_code (hok 0 (by norm_num)) okId (rep_uElt (by norm_num)) rep_id', hid, Nat.beq_refl]
  · obtain ⟨l, hl, p, hp, he⟩ := htree i hi hpos
    refine ⟨l, hl, p, hp, ?_⟩
    rw [eqA_code (hok i hi) (okC_mul (okUG hl) (hok p (hp.trans hi))) (rep_uElt hi)
      (rep_mul (okUG hl) (hok p (hp.trans hi)) (rep_uGen hl) (rep_uElt (hp.trans hi))), he,
      Nat.beq_refl]
  · obtain ⟨j, hj, e⟩ := inL_spec (hcl i hi k hk).1
    refine ⟨j, hj, ?_⟩
    rw [eqA_code (okC_mul (okUG hk) (hok i hi)) (hok j hj)
      (rep_mul (okUG hk) (hok i hi) (rep_uGen hk) (rep_uElt hi)) (rep_uElt hj), e, Nat.beq_refl]
  · obtain ⟨j, hj, e⟩ := inL_spec (hcl i hi k hk).2
    have hgi := (hgen k hk).2.1
    refine ⟨j, hj, ?_⟩
    rw [eqA_code (okC_mul hgi (hok i hi)) (hok j hj)
      (rep_mul hgi (hok i hi) (rep_uGenInv hk) (rep_uElt hi)) (rep_uElt hj), e, Nat.beq_refl]
  · rw [comm_eq (okUG hi) (okUG hj) (rep_uGen hi) (rep_uGen hj)]
    exact hcomm i hi j hj
  · change eqA 240 _ (idA 240) = false
    rw [eqA_code (okC_mul (okUG (by norm_num)) (okUG (by norm_num)))
      okId (rep_mul (okUG (by norm_num)) (okUG (by norm_num)) (rep_uGen (by norm_num))
        (rep_uGen (by norm_num))) rep_id']
    exact beq_false hsq

theorem lr_codes : ∀ a < 8, pg (nat_lit 8) (nat_lit 255) LR a = liftReps.getD a 0 ∧
    liftReps.getD a 0 ∈ [3, 5, 17, 65, 0, 10, 34, 40, 130, 136, 160, 170] := by
  decide +kernel

section Lifts

variable {L : ℕ} (hL : ∀ a < 8, pg (nat_lit 8) (nat_lit 255) L a = liftReps.getD a 0 ∧
    liftReps.getD a 0 ∈ [3, 5, 17, 65, 0, 10, 34, 40, 130, 136, 160, 170])

include hL in
theorem liftReps_all_eq (f : ℕ → Bool) :
    liftReps.all f = allN 8 (fun a => f (pg (nat_lit 8) (nat_lit 255) L a)) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff]
  constructor
  · intro h a ha
    rw [(hL a ha).1]
    exact h _ (getD_mem' (by simpa [liftReps] using ha))
  · intro h r hr
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hr
    have ha' : a < 8 := by simpa [liftReps] using ha
    have := h a ha'
    rwa [(hL a ha').1, List.getD_eq_getElem _ _ ha] at this

include hL in
theorem rep_liftQ {a : ℕ} (ha : a < 8) {q : ℕ} (hq : okC q = true) {σ : Equiv.Perm (Fin 8)}
    (hr : Rep 240 (permArr σ) (Φ q)) :
    okC (liftK (pg (nat_lit 8) (nat_lit 255) L a) q) = true ∧
    Rep 240 (liftArr (pg (nat_lit 8) (nat_lit 255) L a) σ)
      (Φ (liftK (pg (nat_lit 8) (nat_lit 255) L a) q)) := by
  obtain ⟨e, hm⟩ := hL a ha
  rw [e]
  exact ⟨okC_mul (sign_ok _ hm).2.2 hq, rep_mul (sign_ok _ hm).2.2 hq (rep_sign'' hm) hr⟩

theorem lift1_bool (c01 c02 c03 c12 c13 c23 f0 f1 f2 f3 : Bool)
    (h : bIf(bAnd(c01, bAnd(c02, bAnd(c03, bAnd(c12, bAnd(c13, c23))))),
      bAnd(f0, bAnd(f1, bAnd(f2, f3))), true) = true) :
    (!(c01 && c02 && c03 && c12 && c13 && c23) || (f0 && f1 && f2 && f3)) = true := by
  revert h
  revert c01 c02 c03 c12 c13 c23 f0 f1 f2 f3
  decide

theorem lift0_bool (c01 c02 c12 f0 f1 f2 u0 u1 u2 : Bool)
    (h : bIf(bAnd(c01, bAnd(c02, c12)), bIf(bAnd(f0, bAnd(f1, f2)), true,
      bAnd(u0, bAnd(u1, u2))), true) = true) :
    (!(c01 && c02 && c12) || (f0 && f1 && f2) || (u0 && u1 && u2)) = true := by
  revert h
  revert c01 c02 c12 f0 f1 f2 u0 u1 u2
  decide

theorem lift1_of {x0 x1 x2 x3 : ℕ} {t0 t1 t2 t3 : Array ℕ} (o0 : okC x0 = true)
    (o1 : okC x1 = true) (o2 : okC x2 = true) (o3 : okC x3 = true) (r0 : Rep 240 t0 (Φ x0))
    (r1 : Rep 240 t1 (Φ x1)) (r2 : Rep 240 t2 (Φ x2)) (r3 : Rep 240 t3 (Φ x3))
    (hk : bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, bAnd(commB x0 x3, bAnd(commB x1 x2,
      bAnd(commB x1 x3, commB x2 x3))))),
      bAnd(frameK' x0, bAnd(frameK' x1, bAnd(frameK' x2, frameK' x3))), true) = true) :
    (!(commA' t0 t1 && commA' t0 t2 && commA' t0 t3 && commA' t1 t2 && commA' t1 t3 &&
      commA' t2 t3) || (memE1 frameArrs t0 && memE1 frameArrs t1 && memE1 frameArrs t2 &&
        memE1 frameArrs t3)) = true := by
  rw [comm_eq o0 o1 r0 r1, comm_eq o0 o2 r0 r2, comm_eq o0 o3 r0 r3, comm_eq o1 o2 r1 r2,
    comm_eq o1 o3 r1 r3, comm_eq o2 o3 r2 r3, memE1_code o0 r0, memE1_code o1 r1,
    memE1_code o2 r2, memE1_code o3 r3]
  exact lift1_bool _ _ _ _ _ _ _ _ _ _ hk

theorem lift1K_at {L Q : ℕ} (h : lift1K L Q = true) {a b c d : ℕ} (ha : a < 8) (hb : b < 8)
    (hc : c < 8) (hd : d < 8) :
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L a) (e32 Q (nat_lit 0))) (fun x0 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L b) (e32 Q (nat_lit 1))) fun x1 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L c) (e32 Q (nat_lit 2))) fun x2 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L d) (e32 Q (nat_lit 3))) fun x3 =>
      bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, bAnd(commB x0 x3, bAnd(commB x1 x2,
          bAnd(commB x1 x3, commB x2 x3))))),
        bAnd(frameK' x0, bAnd(frameK' x1, bAnd(frameK' x2, frameK' x3))), true)) = true :=
  allN_spec (allN_spec (allN_spec (allN_spec h a ha) b hb) c hc) d hd

theorem strict4 {Y0 Y1 Y2 Y3 : ℕ}
    (hk : strictB Y0 (fun x0 => strictB Y1 fun x1 => strictB Y2 fun x2 => strictB Y3 fun x3 =>
      bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, bAnd(commB x0 x3, bAnd(commB x1 x2,
          bAnd(commB x1 x3, commB x2 x3))))),
        bAnd(frameK' x0, bAnd(frameK' x1, bAnd(frameK' x2, frameK' x3))), true)) = true) :
    bIf(bAnd(commB Y0 Y1, bAnd(commB Y0 Y2, bAnd(commB Y0 Y3, bAnd(commB Y1 Y2,
        bAnd(commB Y1 Y3, commB Y2 Y3))))),
      bAnd(frameK' Y0, bAnd(frameK' Y1, bAnd(frameK' Y2, frameK' Y3))), true) = true := by
  rw [strictB_eq', strictB_eq', strictB_eq', strictB_eq'] at hk
  exact hk

include hL in
theorem lift1_gen {Q : ℕ} (k : lift1K L Q = true) (hq : ∀ j < 4, okC (e32 Q j) = true ∧
    Rep 240 (permArr (q1Gens.getD j 1)) (Φ (e32 Q j))) : lift1Check = true := by
  rw [lift1Check, liftReps_all_eq hL, allN_iff]
  intro a ha
  rw [liftReps_all_eq hL, allN_iff]
  intro b hb
  rw [liftReps_all_eq hL, allN_iff]
  intro c hc
  rw [liftReps_all_eq hL, allN_iff]
  intro d hd
  have hk := strict4 (lift1K_at k ha hb hc hd)
  obtain ⟨o0, r0⟩ := rep_liftQ hL ha (hq (nat_lit 0) (by decide)).1 (hq (nat_lit 0) (by decide)).2
  obtain ⟨o1, r1⟩ := rep_liftQ hL hb (hq (nat_lit 1) (by decide)).1 (hq (nat_lit 1) (by decide)).2
  obtain ⟨o2, r2⟩ := rep_liftQ hL hc (hq (nat_lit 2) (by decide)).1 (hq (nat_lit 2) (by decide)).2
  obtain ⟨o3, r3⟩ := rep_liftQ hL hd (hq (nat_lit 3) (by decide)).1 (hq (nat_lit 3) (by decide)).2
  exact lift1_of o0 o1 o2 o3 r0 r1 r2 r3 hk

theorem strict3 {U Y0 Y1 Y2 : ℕ}
    (hk : strictB Y0 (fun x0 => strictB Y1 fun x1 => strictB Y2 fun x2 =>
      bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, commB x1 x2)),
        bIf(bAnd(frameK' x0, bAnd(frameK' x1, frameK' x2)), true,
          bAnd(inL U (nat_lit 128) x0, bAnd(inL U (nat_lit 128) x1, inL U (nat_lit 128) x2))),
        true)) = true) :
    bIf(bAnd(commB Y0 Y1, bAnd(commB Y0 Y2, commB Y1 Y2)),
      bIf(bAnd(frameK' Y0, bAnd(frameK' Y1, frameK' Y2)), true,
        bAnd(inL U (nat_lit 128) Y0, bAnd(inL U (nat_lit 128) Y1, inL U (nat_lit 128) Y2))),
      true) = true := by
  rw [strictB_eq', strictB_eq', strictB_eq'] at hk
  exact hk

theorem lift0K_at {Q U : ℕ} (h : lift0K L Q U = true) {a b c : ℕ} (ha : a < 8) (hb : b < 8)
    (hc : c < 8) :
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L a) (e32 Q (nat_lit 0))) (fun x0 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L b) (e32 Q (nat_lit 1))) fun x1 =>
    strictB (liftK (pg (nat_lit 8) (nat_lit 255) L c) (e32 Q (nat_lit 2))) fun x2 =>
      bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, commB x1 x2)),
        bIf(bAnd(frameK' x0, bAnd(frameK' x1, frameK' x2)), true,
          bAnd(inL U (nat_lit 128) x0, bAnd(inL U (nat_lit 128) x1, inL U (nat_lit 128) x2))),
        true)) = true :=
  allN_spec (allN_spec (allN_spec h a ha) b hb) c hc

theorem lift0_of {U x0 x1 x2 : ℕ} {t0 t1 t2 : Array ℕ}
    (hU : ∀ {c : ℕ}, okC c = true → ∀ {t : Array ℕ}, Rep 240 t (Φ c) → memU t = inL U 128 c)
    (o0 : okC x0 = true) (o1 : okC x1 = true) (o2 : okC x2 = true) (r0 : Rep 240 t0 (Φ x0))
    (r1 : Rep 240 t1 (Φ x1)) (r2 : Rep 240 t2 (Φ x2))
    (hk : bIf(bAnd(commB x0 x1, bAnd(commB x0 x2, commB x1 x2)),
        bIf(bAnd(frameK' x0, bAnd(frameK' x1, frameK' x2)), true,
          bAnd(inL U (nat_lit 128) x0, bAnd(inL U (nat_lit 128) x1, inL U (nat_lit 128) x2))),
        true) = true) :
    (!(commA' t0 t1 && commA' t0 t2 && commA' t1 t2) ||
      (memE1 frameArrs t0 && memE1 frameArrs t1 && memE1 frameArrs t2) ||
      (memU t0 && memU t1 && memU t2)) = true := by
  rw [comm_eq o0 o1 r0 r1, comm_eq o0 o2 r0 r2, comm_eq o1 o2 r1 r2, memE1_code o0 r0,
    memE1_code o1 r1, memE1_code o2 r2, hU o0 r0, hU o1 r1, hU o2 r2]
  exact lift0_bool _ _ _ _ _ _ _ _ _ hk

include hL in
theorem lift0_gen {Q U : ℕ} (k : lift0K L Q U = true) (hq : ∀ j < 3, okC (e32 Q j) = true ∧
    Rep 240 (permArr (q0Gens.getD j 1)) (Φ (e32 Q j)))
    (hU : ∀ {c : ℕ}, okC c = true → ∀ {t : Array ℕ}, Rep 240 t (Φ c) → memU t = inL U 128 c) :
    lift0Check = true := by
  rw [lift0Check, liftReps_all_eq hL, allN_iff]
  intro a ha
  rw [liftReps_all_eq hL, allN_iff]
  intro b hb
  rw [liftReps_all_eq hL, allN_iff]
  intro c hc
  have hk := strict3 (lift0K_at k ha hb hc)
  obtain ⟨o0, r0⟩ := rep_liftQ hL ha (hq (nat_lit 0) (by decide)).1 (hq (nat_lit 0) (by decide)).2
  obtain ⟨o1, r1⟩ := rep_liftQ hL hb (hq (nat_lit 1) (by decide)).1 (hq (nat_lit 1) (by decide)).2
  obtain ⟨o2, r2⟩ := rep_liftQ hL hc (hq (nat_lit 2) (by decide)).1 (hq (nat_lit 2) (by decide)).2
  exact lift0_of hU o0 o1 o2 r0 r1 r2 hk

end Lifts

theorem memU_code {c : ℕ} (hc : okC c = true) {t : Array ℕ} (ht : Rep 240 t (Φ c)) :
    memU t = inL UC 128 c := by
  rw [Bool.eq_iff_iff, memU, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, he⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hj' : j < 128 := by simpa [uPrimeCert] using hj
    rw [Array.getElem_toList, ← getElem!_pos _ j (by simpa [uPrimeCert] using hj'),
      eqA_code hc (okUC hj') ht (rep_uElt hj')] at he
    rw [inL, notB'_eq, Bool.not_eq_true']
    exact allN_eq_false hj' (by rw [notB'_eq, Nat.eq_of_beq_eq_true he, Nat.beq_refl]; rfl)
  · intro h
    obtain ⟨j, hj, e⟩ := inL_spec h
    have hsz : j < uPrimeCert.pts.size := by simpa [uPrimeCert] using hj
    refine ⟨uPrimeCert.pts[j]!, ?_, ?_⟩
    · rw [getElem!_pos _ j hsz]
      exact Array.getElem_mem_toList hsz
    · rw [eqA_code hc (okUC hj) ht (rep_uElt hj), e, Nat.beq_refl]

theorem lift1_ok : lift1Check = true :=
  lift1_gen lr_codes kLift1 fun _ hj => ⟨okQ.1 _ hj, rep_q1 hj⟩

theorem lift0_ok : lift0Check = true :=
  lift0_gen lr_codes kLift0 (fun _ hj => ⟨okQ.2 _ hj, rep_q0 hj⟩) memU_code

open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3221 : PListFacts
    ∧ SubListFacts pPlusGens pPlusIdx pPlusMask pPlusWords
    ∧ SubListFacts q1Gens q1Idx q1Mask q1Words
    ∧ SubListFacts q0Gens q0Idx q0Mask q0Words
    ∧ LayerFacts
    ∧ (lift1Check = true)
    ∧ (lift0Check = true)
    ∧ UListFacts :=
  ⟨p_list_ok, sub_ok kPlus rfl sub_gens_plus, sub_ok kQ1 rfl sub_gens_q1,
    sub_ok kQ0 rfl sub_gens_q0, layer_ok, lift1_ok, lift0_ok, u_list_ok⟩

end CertificateChecks.KernelLC.W3221

end
