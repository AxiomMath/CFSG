module

public import Certificates.Data.Kernel.OpsMcertN
public import Certificates.Data.Kernel.OpsFpK
public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.Certificates.Kernel.SporSch.LyMatSound
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC.LyNF

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KD.OrdLy CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CFSG.KS.SporSch.LyM (wordR letterR)

@[expose] def ordG (g : Nat) : Nat := if g = 0 then 2 else 5

@[expose] def push : List (Nat × Nat) → Nat × Nat → List (Nat × Nat)
  | [], q => if q.2 % ordG q.1 = 0 then [] else [(q.1, q.2 % ordG q.1)]
  | h :: t, q =>
    if h.1 = q.1 then
      (if (h.2 + q.2) % ordG q.1 = 0 then t else (q.1, (h.2 + q.2) % ordG q.1) :: t)
    else if q.2 % ordG q.1 = 0 then h :: t else (q.1, q.2 % ordG q.1) :: h :: t

section Monoid

variable {M : Type} [Monoid M] (a b : M)

@[expose] def val (q : Nat × Nat) : M := (if q.1 = 0 then a else b) ^ q.2

theorem pow_mod_of {x : M} {n : Nat} (hx : x ^ n = 1) (m : Nat) : x ^ m = x ^ (m % n) := by
  conv_lhs => rw [← Nat.mod_add_div m n]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

theorem base_pow {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 5 = 1) (g : Nat) :
    (if g = 0 then a else b) ^ ordG g = 1 := by
  unfold ordG
  split <;> assumption

theorem prod_push {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 5 = 1) (st : List (Nat × Nat))
    (q : Nat × Nat) :
    (((push st q).reverse.map (val a b)).prod) = (st.reverse.map (val a b)).prod * val a b q := by
  have hm := pow_mod_of (base_pow ha hb q.1)
  have vq : val a b q = (if q.1 = 0 then a else b) ^ q.2 := rfl
  have vr : ∀ r, val a b (q.1, r) = (if q.1 = 0 then a else b) ^ r := fun _ => rfl
  cases st with
  | nil =>
    by_cases h0 : q.2 % ordG q.1 = 0
    · rw [push, ite_eq_left h0]
      simp only [List.reverse_nil, List.map_nil, List.prod_nil, one_mul]
      rw [vq, hm, h0, pow_zero]
    · rw [push, ite_eq_right h0]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul]
      rw [vr, vq, ← hm]
  | cons h t =>
    by_cases he : h.1 = q.1
    · have vh : val a b h = (if q.1 = 0 then a else b) ^ h.2 := by
        change (if h.1 = 0 then a else b) ^ h.2 = _
        rw [he]
      by_cases h0 : (h.2 + q.2) % ordG q.1 = 0
      · rw [push, ite_eq_left he, ite_eq_left h0]
        simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [vh, vq, mul_assoc, ← pow_add, hm, h0, pow_zero, mul_one]
      · rw [push, ite_eq_left he, ite_eq_right h0]
        simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [vh, vq, mul_assoc, ← pow_add, hm (h.2 + q.2), vr]
    · by_cases h0 : q.2 % ordG q.1 = 0
      · rw [push, ite_eq_right he, ite_eq_left h0]
        simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        rw [vq, hm, h0, pow_zero, mul_one]
      · rw [push, ite_eq_right he, ite_eq_right h0]
        simp only [List.reverse_cons, List.map_append, List.prod_append, List.map_cons,
          List.map_nil, List.prod_cons, List.prod_nil, mul_one, List.append_assoc,
          List.singleton_append]
        rw [vr, vq, ← hm, mul_assoc]

theorem prod_fold {a b : M} (ha : a ^ 2 = 1) (hb : b ^ 5 = 1) :
    ∀ (us st : List (Nat × Nat)), ((us.foldl push st).reverse.map (val a b)).prod =
      (st.reverse.map (val a b)).prod * (us.map (val a b)).prod
  | [], st => by simp
  | q :: us, st => by
    rw [List.foldl_cons, prod_fold ha hb us, prod_push ha hb, List.map_cons, List.prod_cons,
      mul_assoc]

end Monoid

local notation "mulL" => mulR 5 12 1332 111 8 L H CM RM

local notation "φ" => CFSG.KS.Ord.ordMat 5 111 12 1332

local notation "Cn" => CFSG.KS.Ord.Canon 5 111 12

theorem canon_of {X : Nat} (h : vld X = true) : Cn X := CFSG.KS.Ord.validM_canon consts h

theorem phi_inj {X Y : Nat} (hX : Cn X) (hY : Cn Y) (h : φ X = φ Y) : X = Y := by
  refine CFSG.KS.SporSch.LyM.canon_ext hX hY fun i hi j hj => ?_
  have e := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  simp only [CFSG.KS.SporSch.LyM.ordMat_apply] at e
  exact CFSG.KS.SporSch.LyM.eq_of_cast (CFSG.KS.SporSch.LyM.canon_ent hX hi hj)
    (CFSG.KS.SporSch.LyM.canon_ent hY hi hj) e

theorem fold_mul : ∀ (vs : List Nat) (X : Nat), Cn X → (∀ v ∈ vs, Cn v) →
    Cn (vs.foldl mulL X) ∧ φ (vs.foldl mulL X) = φ X * (vs.map φ).prod
  | [], X, hX, _ => ⟨hX, by simp⟩
  | v :: vs, X, hX, hv => by
    obtain ⟨c1, e1⟩ := CFSG.KS.Ord.mulR_sound consts hX (hv v (by simp))
    obtain ⟨c2, e2⟩ := fold_mul vs _ c1 fun u hu => hv u (by simp [hu])
    refine ⟨c2, ?_⟩
    rw [List.foldl_cons, e2, e1, List.map_cons, List.prod_cons, mul_assoc]

theorem wordR_fold (G GI : Nat → Nat) : ∀ (us : List Int) (X : Nat),
    wordR 5 12 1332 111 8 L H CM RM G GI X us = (us.map (letterR G GI)).foldl mulL X
  | [], _ => rfl
  | l :: us, X => by
    rw [CFSG.KS.SporSch.LyM.wordR_cons, wordR_fold G GI us, List.map_cons, List.foldl_cons]

@[expose] def lmap (l : Int) : Nat × Nat :=
  if l = 1 then (0, 1) else if l = 2 then (1, 1) else if l = -1 then (0, 1) else (1, 4)

@[expose] def rmap (x : Nat) : Nat × Nat := if x = 0 then (0, 1) else (1, x)

@[expose] def src : Op → Nat
  | .mul _ j _ => j
  | .pow _ i _ => i

@[expose] def isStep (t : Nat) : Op → Bool
  | .mul i j k => i == t && k == t && decide (j < 5)
  | .pow _ _ _ => false

@[expose] def isChain (t : Nat) : List Op → Bool
  | .pow 1 1 k :: tl => k == t && tl.all (isStep t)
  | _ => false

@[expose] def preProg : List Op := lyThreeProg.take 3

@[expose] def seg5 : List Op := (lyThreeProg.drop 3).take 727

@[expose] def seg6 : List Op := ((lyThreeProg.drop 3).drop 727).take 1139

@[expose] def restProg : List Op := ((lyThreeProg.drop 3).drop 727).drop 1139

theorem prog_eq : lyThreeProg = preProg ++ (seg5 ++ (seg6 ++ restProg)) := by
  unfold preProg seg5 seg6 restProg
  rw [List.take_append_drop, List.take_append_drop, List.take_append_drop]

noncomputable abbrev OL : Ops Nat Nat := opsFpK 5 12 1332 111 8 L H CM RM ONE

@[expose] noncomputable def initL1 : List Nat := preProg.foldl (stepL OL) (initN OL A B 61)

@[expose] noncomputable def initL2 : List Nat := (initL1.set 5 (CF 0)).set 6 (CF 1)

theorem chains_ok : (isChain 5 seg5 && isChain 6 seg6) = true := by decide

theorem nf_ok : ((W0.map lmap).foldl push []).reverse = (seg5.map src).map rmap ∧
    ((W1.map lmap).foldl push []).reverse = (seg6.map src).map rmap := by decide

theorem letters_ok : (W0 ++ W1).all (fun l => l == 1 || l == 2 || l == -1 || l == -2) = true := by
  decide

theorem aa_ok : Nat.beq (mulL A A) ONE = true := by quickRfl

theorem bb_ok : Nat.beq (mulL B B4) ONE = true := by quickRfl

theorem regs_ok : (initL1.length == 61 && Nat.beq (getN initL1 0) A && Nat.beq (getN initL1 1) B &&
    Nat.beq (getN initL1 2) (mulL B B) && Nat.beq (getN initL1 3) (mulL (mulL B B) B) &&
    Nat.beq (getN initL1 4) (mulL (mulL (mulL B B) B) B)) = true := by quickRfl

theorem b4_ok : Nat.beq (mulL (mulL (mulL B B) B) B) B4 = true := by quickRfl

theorem step_eq {R : List Nat} {t j X : Nat} (ht : t < R.length) (hne : t ≠ j) :
    stepL OL (R.set t X) (.mul t j t) = R.set t (mulL X (getN R j)) := by
  change (R.set t X).set t (OL.mul (getN (R.set t X) t) (getN (R.set t X) j)) = _
  rw [getN_set_eq ht, getN_set_ne R hne, List.set_set]
  rfl

theorem chain_fold {t : Nat} (h5 : 5 ≤ t) : ∀ (xs : List Op) (R : List Nat) (X : Nat),
    t < R.length → xs.all (isStep t) = true →
    xs.foldl (stepL OL) (R.set t X) = R.set t ((xs.map (fun op => getN R (src op))).foldl mulL X)
  | [], _, _, _, _ => rfl
  | op :: xs, R, X, ht, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases op with
    | mul i j k =>
      simp only [isStep, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨⟨hi, hk⟩, hj⟩ := h1
      subst hi hk
      rw [List.foldl_cons, step_eq ht (by omega), chain_fold h5 xs R _ ht h2]
      rfl
    | pow e i k => simp [isStep] at h1

theorem pow_one' (X : Nat) : OL.pow X 1 = X := by
  rw [Ops.pow]
  simp

theorem src_lt {t : Nat} {seg : List Op} (hs : isChain t seg = true) : ∀ op ∈ seg, src op < 5 := by
  match seg, hs with
  | .pow 1 1 k :: tl, hs =>
    simp only [isChain, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hs
    intro op hop
    rcases List.mem_cons.1 hop with rfl | hop
    · simp [src]
    · have := hs.2 op hop
      cases op with
      | mul i j k =>
        simp only [isStep, Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.2
      | pow e i k => simp [isStep] at this

theorem seg_fold {t : Nat} (h5 : 5 ≤ t) {seg : List Op} (hs : isChain t seg = true)
    (R : List Nat) (ht : t < R.length) (hR : ∀ x < 5, Cn (getN R x)) :
    ∃ v, seg.foldl (stepL OL) R = R.set t v ∧ Cn v ∧
      φ v = (seg.map (fun op => φ (getN R (src op)))).prod := by
  match seg, hs with
  | .pow 1 1 k :: tl, hs =>
    have hs' := hs
    simp only [isChain, Bool.and_eq_true, beq_iff_eq] at hs'
    obtain ⟨rfl, htl⟩ := hs'
    have e0 : stepL OL R (.pow 1 1 k) = R.set k (getN R 1) := by
      change R.set k (OL.pow (getN R 1) 1) = _
      rw [pow_one']
    have hlt := src_lt hs
    obtain ⟨c, e⟩ := fold_mul (tl.map fun op => getN R (src op)) (getN R 1) (hR 1 (by norm_num))
      (fun v hv => by
        obtain ⟨op, hop, rfl⟩ := List.mem_map.1 hv
        exact hR _ (hlt op (List.mem_cons_of_mem _ hop)))
    refine ⟨_, ?_, c, ?_⟩
    · rw [List.foldl_cons, e0, chain_fold h5 tl R _ ht htl]
    · rw [e, List.map_cons, List.prod_cons, List.map_map]
      rfl

theorem cOne : Cn ONE ∧ φ ONE = 1 := CFSG.KS.Ord.one_sound consts

theorem phi_mul {X Y : Nat} (hX : Cn X) (hY : Cn Y) :
    Cn (mulL X Y) ∧ φ (mulL X Y) = φ X * φ Y :=
  CFSG.KS.Ord.mulR_sound consts hX hY

theorem rel_a : φ A ^ 2 = 1 := by
  rw [pow_two, ← (phi_mul (canon_of vA) (canon_of vA)).2, Nat.eq_of_beq_eq_true aa_ok, cOne.2]

theorem phi_b4 : φ B4 = φ B ^ 4 := by
  have h1 := phi_mul (canon_of vB) (canon_of vB)
  have h2 := phi_mul h1.1 (canon_of vB)
  have h3 := phi_mul h2.1 (canon_of vB)
  rw [← Nat.eq_of_beq_eq_true b4_ok, h3.2, h2.2, h1.2,
    show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add, pow_one]

theorem rel_b : φ B ^ 5 = 1 := by
  rw [pow_succ', ← phi_b4, ← (phi_mul (canon_of vB) (canon_of vB4)).2,
    Nat.eq_of_beq_eq_true bb_ok, cOne.2]

theorem word_val {W : List Int}
    (hW : ∀ l ∈ W, Cn (letterR GS GSI l) ∧ φ (letterR GS GSI l) = val (φ A) (φ B) (lmap l)) :
    Cn (wordR 5 12 1332 111 8 L H CM RM GS GSI ONE W) ∧
      φ (wordR 5 12 1332 111 8 L H CM RM GS GSI ONE W) = ((W.map lmap).map (val (φ A) (φ B))).prod := by
  rw [wordR_fold]
  obtain ⟨c, e⟩ := fold_mul (W.map (letterR GS GSI)) ONE cOne.1 (fun v hv => by
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hv
    exact (hW l hl).1)
  refine ⟨c, ?_⟩
  rw [e, cOne.2, one_mul, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun l hl => (hW l hl).2

theorem chain_val {t : Nat} (h5 : 5 ≤ t) {seg : List Op} (hs : isChain t seg = true)
    (R : List Nat) (ht : t < R.length)
    (hR : ∀ x < 5, Cn (getN R x) ∧ φ (getN R x) = val (φ A) (φ B) (rmap x)) {W : List Int}
    (hW : ∀ l ∈ W, Cn (letterR GS GSI l) ∧ φ (letterR GS GSI l) = val (φ A) (φ B) (lmap l))
    (hnf : ((W.map lmap).foldl push []).reverse = (seg.map src).map rmap) {Z : Nat}
    (hZ : wordR 5 12 1332 111 8 L H CM RM GS GSI ONE W = Z) :
    seg.foldl (stepL OL) R = R.set t Z := by
  obtain ⟨v, e, cv, ev⟩ := seg_fold h5 hs R ht (fun x hx => (hR x hx).1)
  obtain ⟨cZ, eZ⟩ := word_val hW
  rw [hZ] at cZ eZ
  rw [e, phi_inj cv cZ ?_]
  have hp := prod_fold rel_a rel_b (W.map lmap) []
  rw [hnf, List.reverse_nil, List.map_nil, List.prod_nil, one_mul] at hp
  rw [ev, eZ, ← hp, List.map_map, List.map_map]
  congr 1
  exact List.map_congr_left fun op hop => (hR _ (src_lt hs op hop)).2

theorem chunks {G GI K : Nat → Nat} {W : List Int} {m c : Nat}
    (h : ∀ k < m, Nat.beq (wordR 5 12 1332 111 8 L H CM RM G GI (K k)
      (List.take c (List.drop (Nat.mul k c) W))) (K (Nat.succ k)) = true)
    (hl : W.length ≤ m * c) :
    wordR 5 12 1332 111 8 L H CM RM G GI (K 0) W = K m := by
  have key : ∀ j ≤ m, wordR 5 12 1332 111 8 L H CM RM G GI (K (m - j))
      (W.drop ((m - j) * c)) = K m := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_eq_nil_of_le hl]
      rfl
    | succ j ih =>
      intro hj
      have e : m - j = (m - (j + 1)) + 1 := by omega
      have hk := Nat.eq_of_beq_eq_true (h (m - (j + 1)) (by omega))
      rw [← List.take_append_drop c (W.drop ((m - (j + 1)) * c)),
        CFSG.KS.SporSch.LyM.wordR_append, List.drop_drop]
      have hm : Nat.mul (m - (j + 1)) c = (m - (j + 1)) * c := rfl
      rw [hm] at hk
      rw [hk, ← ih (by omega), e, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
  have := key m le_rfl
  rwa [Nat.sub_self, Nat.zero_mul, List.drop_zero] at this

theorem hw0 : wordR 5 12 1332 111 8 L H CM RM GS GSI ONE W0 = CF 0 := by
  have hm : K0.m = 84 := rfl
  have hk := Nat.eq_of_beq_eq_true k0m
  rw [hm] at hk
  rw [← Nat.eq_of_beq_eq_true k00, chunks K0.all (by simpa [hm] using Nat.le_of_ble_eq_true len0),
    hk]

theorem hw1 : wordR 5 12 1332 111 8 L H CM RM GS GSI ONE W1 = CF 1 := by
  have hm : K1.m = 124 := rfl
  have hk := Nat.eq_of_beq_eq_true k1m
  rw [hm] at hk
  rw [← Nat.eq_of_beq_eq_true k10, chunks K1.all (by simpa [hm] using Nat.le_of_ble_eq_true len1),
    hk]

theorem letters_val : ∀ l ∈ W0 ++ W1,
    Cn (letterR GS GSI l) ∧ φ (letterR GS GSI l) = val (φ A) (φ B) (lmap l) := by
  intro l hl
  have h := List.all_eq_true.1 letters_ok l hl
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((rfl | rfl) | rfl) | rfl
  · exact ⟨canon_of vA, by simp [lmap, val]; rfl⟩
  · exact ⟨canon_of vB, by simp [lmap, val]; rfl⟩
  · exact ⟨canon_of vA, by simp [lmap, val]; rfl⟩
  · exact ⟨canon_of vB4, by simp [lmap, val, ← phi_b4]; rfl⟩

theorem regs_val : initL1.length = 61 ∧
    ∀ x < 5, Cn (getN initL1 x) ∧ φ (getN initL1 x) = val (φ A) (φ B) (rmap x) := by
  have hr := regs_ok
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨hl, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hr
  have cb := canon_of vB
  have m2 := phi_mul cb cb
  have m3 := phi_mul m2.1 cb
  have m4 := phi_mul m3.1 cb
  refine ⟨hl, fun x hx => ?_⟩
  interval_cases x
  · rw [Nat.eq_of_beq_eq_true h0]
    exact ⟨canon_of vA, by simp [rmap, val]⟩
  · rw [Nat.eq_of_beq_eq_true h1]
    exact ⟨cb, by simp [rmap, val]⟩
  · rw [Nat.eq_of_beq_eq_true h2]
    exact ⟨m2.1, by rw [m2.2]; simp [rmap, val, pow_two]⟩
  · rw [Nat.eq_of_beq_eq_true h3]
    exact ⟨m3.1, by rw [m3.2, m2.2]; simp [rmap, val, pow_succ]⟩
  · rw [Nat.eq_of_beq_eq_true h4]
    exact ⟨m4.1, by rw [m4.2, m3.2, m2.2]; simp [rmap, val, pow_succ]⟩

theorem mid_eq : seg6.foldl (stepL OL) (seg5.foldl (stepL OL) initL1) = initL2 := by
  obtain ⟨hl, hR⟩ := regs_val
  have hc := chains_ok
  simp only [Bool.and_eq_true] at hc
  rw [chain_val (by norm_num) hc.1 initL1 (by rw [hl]; norm_num) hR
      (fun l hl => letters_val l (List.mem_append_left _ hl)) nf_ok.1 hw0,
    chain_val (by norm_num) hc.2 (initL1.set 5 (CF 0)) (by rw [List.length_set, hl]; norm_num)
      (fun x hx => by rw [getN_set_ne _ (by omega)]; exact hR x hx)
      (fun l hl => letters_val l (List.mem_append_right _ hl)) nf_ok.2 hw1]
  rfl

theorem regsN_eq_rest (k : List Nat → Bool) :
    regsN OL A B lyThreeN lyThreeProg k = runN OL restProg initL2 k := by
  rw [regsN_eq, prog_eq, List.foldl_append, List.foldl_append, List.foldl_append, runN_eq]
  change k (restProg.foldl (stepL OL) (seg6.foldl (stepL OL) (seg5.foldl (stepL OL) initL1))) = _
  rw [mid_eq]

end CertificateChecks.KernelMC.LyNF

end
