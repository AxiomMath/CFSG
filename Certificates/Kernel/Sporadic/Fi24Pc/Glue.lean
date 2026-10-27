module

public import Certificates.Kernel.Sporadic.Fi24Pc.Data
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.N
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.R
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.P0
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.P1
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.P2
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.F
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.X0
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.X1
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.X2
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.X3
public import Certificates.Kernel.Sporadic.Fi24Net.Letters
public import CFSG.Certificates.Kernel.Spor.Fi24PcSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24ThreeClasses
public import CFSG.Certificates.Kernel.Spor.Fi24FixSound
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CFSG.KD.Fi24Pc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KC.Fi24Pc CFSG.KS.Fi24Net
  CFSG.KS.Fi24NetPt CFSG.KS.Fi24Pc

#kc_forall_tree nAll (fun j => nck j = true) 16 CFSG.KD.Fi24Pc.Ck.n
#kc_forall_tree wAll (fun g => wck g = true) 304 CFSG.KD.Fi24Pc.Ck.w
#kc_forall_tree rAll (fun j => rck j = true) 16 CFSG.KD.Fi24Pc.Ck.r
#kc_forall_tree tAll (fun k => tck k = true) 16 CFSG.KD.Fi24Pc.Ck.t
#kc_forall_tree bAll (fun l => bck l = true) 7 CFSG.KD.Fi24Pc.Ck.b
#kc_forall_tree kAll (fun i => kck i = true) 16 CFSG.KD.Fi24Pc.Ck.k
#kc_forall_tree pAll (fun g => pck g = true) 512 CFSG.KD.Fi24Pc.Ck.p
#kc_forall_tree fAll (fun g => fck g = true) 17 CFSG.KD.Fi24Pc.Ck.f
#kc_forall_tree xAll (fun g => xck g = true) 103 CFSG.KD.Fi24Pc.Ck.x

@[expose] noncomputable def dck (m : Nat) : Bool :=
  andB (Nat.blt (Nat.land (nth J.defs m) 255) (Nat.add m 4)) (Nat.blt (Nat.shiftRight (nth J.defs m) 8) 4)

@[expose] noncomputable def sck : Bool :=
  andB (Nat.beq (lenL J.B) 7) (andB (Nat.beq (lenL (nthL J.levels 16)) (lenL J.fin))
    (andB (eqL (nthL J.levels 0) [0]) (andB (Nat.blt (lenL (nthL J.levels 16)) 1089)
      (andB (allBelow 16 1 (fun i => Nat.blt (lenL (nthL J.levels i)) 2049))
        (andB (Nat.beq (lenL (nthL J.orb 0)) 729) (andB (Nat.beq (lenL (nthL J.orb 1)) 81)
          (andB (Nat.beq (lenL (nthL J.orb 2)) 9) (andB (Nat.beq (lenL (nthL J.orb 3)) 3)
            (andB (Nat.beq (lenL (nthL J.orb 4)) 3) (andB (Nat.beq (lenL (nthL J.orb 5)) 3)
              (Nat.beq (lenL (nthL J.orb 6)) 3)))))))))))

#kc_slice_range CFSG.KD.Fi24Pc.dck Ck.d 0 12
#kc_forall_tree dAll (fun m => dck m = true) 12 CFSG.KD.Fi24Pc.Ck.d

theorem sck_ok : sck = true := by quickRfl

@[expose] noncomputable def bLt : Bool := allBelow 7 1 (fun m => Nat.blt (nth J.B m) 729)

theorem bLt_ok : bLt = true := by quickRfl

@[expose] noncomputable def twck : Bool :=
  andB (eqL (nthL J.tw 0) [18]) (andB (eqL (nthL J.tw 1) [16, 19])
    (andB (eqL (nthL J.tw 2) [14, 16, 16, 14, 16, 16]) (andB (eqL (nthL J.tw 3) [16])
      (eqL (nthL J.tw 4) [2]))))

theorem twck_ok : twck = true := by quickRfl

theorem nthL_mem {ws : List (List Nat)} {j : Nat} : nthL ws j ∈ ws ∨ nthL ws j = [] := by
  induction ws generalizing j with
  | nil => exact Or.inr rfl
  | cons w ws ih =>
    cases j with
    | zero => exact Or.inl List.mem_cons_self
    | succ j =>
      rcases ih (j := j) with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

theorem letW_spec : ∀ {w : List Nat}, List.rec (motive := fun _ => Bool) true
    (fun l _ ih2 => bAnd(Nat.blt l (nat_lit 26), ih2)) w = true → ∀ l ∈ w, l < 26
  | [], _ => by simp
  | a :: v, h => by
    have h2 : (Nat.blt a 26 && List.rec (motive := fun _ => Bool) true
        (fun l _ ih2 => bAnd(Nat.blt l (nat_lit 26), ih2)) v) = true := by
      rw [← bAnd_eq]; exact h
    rw [Bool.and_eq_true, blt_iff] at h2
    intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h2.1
    · exact letW_spec h2.2 l hl

theorem letOK_spec {ws : List (List Nat)} (h : letOK ws = true) : ∀ w ∈ ws, ∀ l ∈ w, l < 26 := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    have h' : ((List.rec (motive := fun _ => Bool) true
        (fun l _ ih2 => bAnd(Nat.blt l (nat_lit 26), ih2)) w) && letOK ws) = true := by
      rw [← bAnd_eq]; exact h
    rw [Bool.and_eq_true] at h'
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact letW_spec h'.1
    · exact ih h'.2 v hv

theorem nthL_lt26 {ws : List (List Nat)} (h : letOK ws = true) (j : Nat) : ∀ l ∈ nthL ws j, l < 26 := by
  rcases nthL_mem (ws := ws) (j := j) with hm | hm
  · exact letOK_spec h _ hm
  · rw [hm]; simp

theorem lck_spec : (∀ j, ∀ l ∈ nthL J.words j, l < 26) ∧ (∀ j, ∀ l ∈ nthL J.trans j, l < 26) ∧
    ∀ j, ∀ l ∈ nthL J.tw j, l < 26 := by
  have h := CFSG.KD.Fi24Pc.Ck.l
  unfold lck at h
  rw [andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨nthL_lt26 h.1, nthL_lt26 h.2.1, nthL_lt26 h.2.2⟩

theorem nv_XW {j : Nat} (hj : j < 16) : NV (XW j) := (net_spec (nAll j hj)).1

theorem XW_perm {j : Nat} (hj : j < 16) {p : Nat} (hp : p < 306936) :
    pF (XW j) p < 306936 ∧ pR (XW j) p < 306936 ∧ pF (XW j) (pR (XW j) p) = p := by
  obtain ⟨hv, hb⟩ := net_spec (nAll j hj)
  have hp19 : p < 524288 := by omega
  have hR := pR_lt hv hp19
  refine ⟨(hb p hp19).2 hp, ?_, pF_pR hv p⟩
  have := (hb _ hR).1
  rw [pF_pR hv p] at this
  exact this hp

theorem pcw_all {j : Nat} (hj : j < 16) : ∀ k < 19, pcwOK CFSG.KD.Fi24Net.NW XW J.words J.defs j k = true := by
  intro k hk
  have := wAll (19 * j + k) (show 19 * j + k < 304 by omega)
  unfold wck at this
  rwa [show Nat.div (19 * j + k) 19 = j by change (19 * j + k) / 19 = j; omega,
    show Nat.mod (19 * j + k) 19 = k by change (19 * j + k) % 19 = k; omega] at this

theorem defs_lt {j : Nat} (hj4 : 4 ≤ j) (hj : j < 16) :
    nth J.defs (j - 4) % 256 < j ∧ nth J.defs (j - 4) / 256 < 4 := by
  have h := dAll (j - 4) (show j - 4 < 12 by omega)
  unfold dck at h
  rw [andB_eq, Bool.and_eq_true, blt_iff, blt_iff] at h
  have e1 : Nat.land (nth J.defs (j - 4)) 255 = nth J.defs (j - 4) % 256 := by
    change _ &&& (2 ^ 8 - 1) = _; rw [Nat.and_two_pow_sub_one_eq_mod]
  have e2 : Nat.shiftRight (nth J.defs (j - 4)) 8 = nth J.defs (j - 4) / 256 := Nat.shiftRight_eq_div_pow _ 8
  rw [e1, e2] at h
  exact ⟨by have := h.1; change _ < j - 4 + 4 at this; omega, h.2⟩

theorem genW_lt {j : Nat} (hj : j < 4) : genW J.words J.defs j = nthL J.words j := by
  unfold genW
  rw [blt_iff.2 hj]

theorem genW_ge {j : Nat} (hj : 4 ≤ j) : genW J.words J.defs j =
    [2 * (nth J.defs (j - 4) % 256) + 1, 2 * (nth J.defs (j - 4) / 256) + 1, 2 * (nth J.defs (j - 4) % 256),
      2 * (nth J.defs (j - 4) / 256)] := by
  unfold genW
  have hb : Nat.blt j 4 = false := by
    cases e : Nat.blt j 4
    · rfl
    · exact absurd (blt_iff.1 e) (by omega)
  rw [hb]
  change commL (nth J.defs (j - 4)) = _
  unfold commL
  have e1 : Nat.land (nth J.defs (j - 4)) 255 = nth J.defs (j - 4) % 256 := by
    change _ &&& (2 ^ 8 - 1) = _; rw [Nat.and_two_pow_sub_one_eq_mod]
  have e2 : Nat.shiftRight (nth J.defs (j - 4)) 8 = nth J.defs (j - 4) / 256 := Nat.shiftRight_eq_div_pow _ 8
  rw [e1, e2]
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_one, mul_comm, Nat.add_eq]

section J


open CFSG.Sporadic.Th CFSG.Perm CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open scoped Pointwise

@[expose] noncomputable def xg (j : ℕ) : CFSG.Sporadic.Fi24.J :=
  if j < 4 then wordElt (nthL J.words j)
  else if h : nth J.defs (j - 4) % 256 < j ∧ nth J.defs (j - 4) / 256 < j then
    (xg (nth J.defs (j - 4) % 256))⁻¹ * (xg (nth J.defs (j - 4) / 256))⁻¹ *
      xg (nth J.defs (j - 4) % 256) * xg (nth J.defs (j - 4) / 256)
  else 1
termination_by j
decreasing_by all_goals omega

variable (hL : ∀ l < 26, ∀ p < 306936, idx 306936 (pairG CFSG.Sporadic.Fi24.gs l) p = LN CFSG.KD.Fi24Net.NW l p)
include hL

theorem idx_wordElt : ∀ w : List ℕ, (∀ l ∈ w, l < 26) → ∀ p < 306936,
    idx 306936 (wordElt w) p = w.foldr (LN CFSG.KD.Fi24Net.NW) p
  | [], _, p, _ => by
    unfold wordElt
    rw [List.map_nil, List.prod_nil, idx_one]
    rfl
  | l :: w, hw, p, hp => by
    have e : wordElt (l :: w) = pairG CFSG.Sporadic.Fi24.gs l * wordElt w := by
      unfold wordElt; rw [List.map_cons, List.prod_cons]
    rw [e, idx_mul, idx_wordElt w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) p hp,
      hL l (hw l List.mem_cons_self) _ ?_, List.foldr_cons]
    rw [← idx_wordElt w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) p hp]
    exact idx_lt _ hp

theorem idx_inv_of {g : CFSG.Sporadic.Fi24.J} {j : Nat} (hj : j < 16)
    (h : ∀ p < 306936, idx 306936 g p = pF (XW j) p) : ∀ p < 306936, idx 306936 g⁻¹ p = pR (XW j) p := by
  intro p hp
  obtain ⟨-, h2, h3⟩ := XW_perm hj hp
  have := idx_inv_idx (n := 306936) g (pR (XW j) p)
  rwa [h _ h2, h3] at this

theorem idx_xg : ∀ j < 16, ∀ p < 306936, idx 306936 (xg j) p = pF (XW j) p := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj p hp
    have hpw := pcw_spec (nv_XW hj) ?_ (pcw_all hj)
    rotate_left
    · intro l hl
      by_cases h4 : j < 4
      · rw [if_pos h4]
        rw [genW_lt h4] at hl
        have := lck_spec.1 j l hl
        exact (net_spec (CFSG.KD.Fi24Net.nck_spec _ (show l / 2 < 13 by omega))).1
      · rw [if_neg h4]
        rw [genW_ge (by omega)] at hl
        have ⟨ha, hb⟩ := defs_lt (by omega) hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> exact nv_XW (by omega)
    rw [hpw p (by omega)]
    by_cases h4 : j < 4
    · rw [if_pos h4, genW_lt h4]
      unfold xg
      rw [if_pos h4]
      exact idx_wordElt hL _ (lck_spec.1 j) p hp
    · rw [if_neg h4, genW_ge (by omega)]
      obtain ⟨ha, hb⟩ := defs_lt (by omega) hj
      rw [xg, if_neg h4, dif_pos ⟨ha, by omega⟩]
      generalize nth J.defs (j - 4) % 256 = a at ha ⊢
      generalize nth J.defs (j - 4) / 256 = b at hb ⊢
      have iha := ih a ha (by omega)
      have ihb := ih b (by omega) (by omega)
      have q1 := (XW_perm (show b < 16 by omega) hp).1
      have q2 := (XW_perm (show a < 16 by omega) q1).1
      have q3 := (XW_perm (show b < 16 by omega) q2).2.1
      rw [idx_mul, idx_mul, idx_mul, ihb p hp, iha _ q1, idx_inv_of hL (by omega) ihb _ q2,
        idx_inv_of hL (by omega) iha _ q3]
      simp only [List.foldr_cons, List.foldr_nil, LN_odd, LN_even]

@[expose] noncomputable def pcl (l : ℕ) : CFSG.Sporadic.Fi24.J :=
  if l % 2 = 0 then xg (l / 2) else (xg (l / 2))⁻¹

@[expose] noncomputable def actJ (g : CFSG.Sporadic.Fi24.J) (p : ℕ) : ℕ := idx 306936 g p

omit hL in
theorem act_mul : ∀ (g h : CFSG.Sporadic.Fi24.J) (p : ℕ), actJ (g * h) p = actJ g (actJ h p) :=
  fun g h p => idx_mul g h p

omit hL in
theorem act_one : ∀ p : ℕ, actJ (1 : CFSG.Sporadic.Fi24.J) p = p := fun p => idx_one p

theorem foldr_letN : ∀ (w : List ℕ), (∀ l ∈ w, l < 32) → ∀ p < 306936,
    w.foldr (letN XW) p = idx 306936 (w.map pcl).prod p ∧ w.foldr (letN XW) p < 306936
  | [], _, p, hp => ⟨by rw [List.map_nil, List.prod_nil, idx_one]; rfl, hp⟩
  | l :: w, hw, p, hp => by
    obtain ⟨i1, i2⟩ := foldr_letN w (fun l' h' => hw l' (List.mem_cons_of_mem _ h')) p hp
    have hl := hw l List.mem_cons_self
    rw [List.foldr_cons, List.map_cons, List.prod_cons, idx_mul, ← i1, letN_eq]
    unfold LN pcl
    by_cases he : l % 2 = 0
    · rw [if_pos he, if_pos he, idx_xg hL _ (by omega) _ i2]
      exact ⟨rfl, (XW_perm (by omega) i2).1⟩
    · rw [if_neg he, if_neg he, idx_inv_of hL (by omega) (idx_xg hL _ (by omega)) _ i2]
      exact ⟨rfl, (XW_perm (by omega) i2).2.1⟩

set_option maxRecDepth 20000 in
theorem nwL_idx {u : ℕ} (hu : ∀ k, dg u k < 3) {p : ℕ} (hp : p < 306936) :
    (nwL u).foldr (letN XW) p = idx 306936 (nv xg u) p := by
  have h1 := (foldr_letN hL _ (nwL_lt u) p hp).1
  have h2 := act_prod actJ (fun g h p => idx_mul g h p) (fun p => idx_one p) ((nwL u).map pcl) p
  have h3 := nwL_act actJ (fun g h p => idx_mul g h p) (fun p => idx_one p) xg
    (fun l q => actJ (pcl l) q)
    (fun k _ q => by
      change actJ (pcl (2 * k)) q = actJ (xg k) q
      unfold pcl; rw [if_pos (by omega), show 2 * k / 2 = k by omega]) hu p
  rw [h1]
  change actJ ((nwL u).map pcl).prod p = actJ (nv xg u) p
  rw [h2, List.foldr_map]
  exact h3

omit hL in
theorem cb_lt : ∀ b ∈ cb, b < 306936 := by decide

omit hL in
theorem chainBase_mem : ∀ t < CFSG.Sporadic.Fi24.Native.chainBase.size,
    CFSG.Sporadic.Fi24.Native.chainBase[t]! ∈ cb := by decide

omit hL in
theorem eq_of_cb {g h : CFSG.Sporadic.Fi24.J} (hgh : ∀ b ∈ cb, idx 306936 g b = idx 306936 h b) :
    g = h := by
  have : h⁻¹ * g = 1 := CFSG.Sporadic.Fi24.sep _ fun t ht => by
    rw [idx_mul, hgh _ (chainBase_mem t ht), idx_inv_idx]
  rw [inv_mul_eq_one] at this
  exact this.symm

omit hL in
theorem pcl_even (j : ℕ) : pcl (2 * j) = xg j := by
  unfold pcl; rw [if_pos (by omega), show 2 * j / 2 = j by omega]

omit hL in
theorem pcl_odd (j : ℕ) : pcl (2 * j + 1) = (xg j)⁻¹ := by
  unfold pcl; rw [if_neg (by omega), show (2 * j + 1) / 2 = j by omega]

theorem word_eq_nv {w : List ℕ} (hw : ∀ l ∈ w, l < 32) {u : ℕ} (hu : ∀ k, dg u k < 3)
    (h : eqP (letN XW) cb w (nwL u) = true) : (w.map pcl).prod = nv xg u := by
  apply eq_of_cb
  intro b hb
  have e := eqP_spec h b hb
  rw [(foldr_letN hL w hw b (cb_lt b hb)).1, nwL_idx hL hu (cb_lt b hb)] at e
  exact e

theorem pres : PcPres xg (fun j => f32 J.PW j) (fun j k => f32 J.CJ (16 * j + k)) := by
  refine ⟨fun j hj => ?_, fun j hj k hk => ?_, fun j k hjk hk => ?_, fun j k hjk hk => ?_,
    fun j k hjk hk => ?_⟩
  · obtain ⟨⟨h1, -, h3⟩, -⟩ := relOK_spec (rAll j hj)
    have := word_eq_nv hL (w := [2 * j, 2 * j, 2 * j]) (by intro l hl; simp at hl; omega)
      (nwOK_spec h1).2 h3
    rw [← this]
    simp [pcl_even, pow_succ, mul_assoc]
  · obtain ⟨⟨-, h2, -⟩, -⟩ := relOK_spec (rAll j hj)
    exact land_lowM_eq_zero.1 h2 k (by omega)
  · obtain ⟨-, h⟩ := relOK_spec (rAll j (show j < 16 by omega))
    obtain ⟨h1, -, h3⟩ := h k hjk hk
    have := word_eq_nv hL (w := [2 * j + 1, 2 * k, 2 * j]) (by intro l hl; simp at hl; omega)
      (nwOK_spec h1).2 h3
    rw [← this]
    simp [pcl_even, pcl_odd, mul_assoc]
  · obtain ⟨-, h⟩ := relOK_spec (rAll j (show j < 16 by omega))
    exact (land_lowM_eq_gw (h k hjk hk).2.1).1
  · obtain ⟨-, h⟩ := relOK_spec (rAll j (show j < 16 by omega))
    exact (land_lowM_eq_gw (h k hjk hk).2.1).2

omit hL in
theorem oFacts : (∀ a < 729, opt J.OP a < 306936) ∧
    ∀ a < 729, ∀ b < 729, opt J.OP a = opt J.OP b → a = b := by
  have h := tAll 0 (show 0 < 16 by omega)
  unfold tck at h
  rw [andB_eq, Bool.and_eq_true] at h
  exact oOK_spec h.1

theorem tabF : TabF actJ xg J.OP J.TB := by
  intro k hk a ha
  have h := tAll k (show k < 16 by omega)
  unfold tck at h
  rw [andB_eq, Bool.and_eq_true] at h
  obtain ⟨t1, t2, t3⟩ := tabOK_spec (CFSG.KC.Fi24FixS.allBelow_spec h.2 (by norm_num) a ha)
  refine ⟨t1, ?_, t3⟩
  rw [← t2, letN_eq, LN_even]
  exact (idx_xg hL k hk _ (oFacts.1 a ha)).symm

omit hL in
theorem nth_B_lt {m : ℕ} (hm : m < 7) : nth J.B m < 729 := by
  have := CFSG.KC.Fi24FixS.allBelow_spec bLt_ok (by norm_num) m hm
  exact blt_iff.1 this

omit hL in
@[expose] noncomputable def bpt (m : ℕ) : Fin 306936 :=
  ⟨opt J.OP (nth J.B (min m 6)), oFacts.1 _ (nth_B_lt (by omega))⟩

omit hL in
theorem bpt_val {m : ℕ} (hm : m < 7) : (bpt m).val = opt J.OP (nth J.B m) := by
  change opt J.OP (nth J.B (min m 6)) = _
  rw [min_eq_left (by omega : m ≤ 6)]

omit hL in
theorem getElem!_nth : ∀ (B : List ℕ) (m : ℕ), B[m]! = nth B m
  | [], m => by cases m <;> rfl
  | b :: B, 0 => rfl
  | b :: B, m + 1 => by
    rw [List.getElem!_cons_succ, getElem!_nth B m]
    rfl

@[expose] noncomputable def Hl (l : ℕ) : Subgroup CFSG.Sporadic.Fi24.J :=
  Subgroup.closure (nv xg '' {g | g ∈ nthL J.gens l})

omit hL in
theorem Hl_le (l : ℕ) : Hl l ≤ Nsub xg 0 :=
  (Subgroup.closure_le _).2 fun _ ⟨u, _, e⟩ => e ▸ nv_mem fun _ h => absurd h (Nat.not_lt_zero _)

omit hL in
theorem smul_val (g : CFSG.Sporadic.Fi24.J) (p : Fin 306936) : (g • p).val = idx 306936 g p.val := by
  rw [idx_of_lt g p.isLt]

omit hL in
theorem orb_lens : (nthL J.orb 0).length = 729 ∧ (nthL J.orb 1).length = 81 ∧
    (nthL J.orb 2).length = 9 ∧ (nthL J.orb 3).length = 3 ∧ (nthL J.orb 4).length = 3 ∧
    (nthL J.orb 5).length = 3 ∧ (nthL J.orb 6).length = 3 := by
  have := sck_ok
  unfold sck at this
  simp only [andB_eq, Bool.and_eq_true, beq_iff, lenL_eq] at this
  exact ⟨this.2.2.2.2.2.1, this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.1,
    this.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2.2.2.2.2⟩

omit hL in
theorem orb_len_le {l : ℕ} (hl : l < 7) : (nthL J.orb l).length ≤ 729 := by
  obtain ⟨l0, l1, l2, l3, l4, l5, l6⟩ := orb_lens
  interval_cases l <;> omega

theorem gens_fix {l : ℕ} (hl : l < 7) : ∀ g ∈ Hl l, ∀ m < l, g • bpt m = bpt m := by
  obtain ⟨h1, -⟩ := orbOK_spec_ (orb_len_le hl) (bAll l (show l < 7 by omega))
  intro g hg m hm
  have hlen : J.B.length = 7 := by
    have := sck_ok
    unfold sck at this
    rw [andB_eq, Bool.and_eq_true, beq_iff, lenL_eq] at this
    exact this.1
  have key : Hl l ≤ MulAction.stabilizer CFSG.Sporadic.Fi24.J (bpt m) := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hn, hf⟩ := h1 u hu
    have e := hf m hm (by omega)
    rw [getElem!_nth] at e
    have ev := (evO_spec actJ (fun g h p => idx_mul g h p) (fun p => idx_one p) (tabF hL)
      (nwOK_spec hn).2 (nth_B_lt (show m < 7 by omega))).2
    rw [e] at ev
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    apply Fin.ext
    rw [smul_val, bpt_val (by omega)]
    exact ev.symm
  exact MulAction.mem_stabilizer_iff.1 (key hg)

theorem reach {l : ℕ} (hgs : ∀ g ∈ nthL J.gens l, nwOK g = true) {b a : ℕ} (hb : b < 729)
    (h : OReach J.TB (nthL J.gens l) b a) :
    a < 729 ∧ ∃ g ∈ Hl l, idx 306936 g (opt J.OP b) = opt J.OP a := by
  induction h with
  | base => exact ⟨hb, 1, one_mem _, idx_one _⟩
  | step u hu _ ih =>
    obtain ⟨h1, g, hg, hge⟩ := ih
    obtain ⟨e1, e2⟩ := evO_spec actJ (fun g h p => idx_mul g h p) (fun p => idx_one p) (tabF hL)
      (nwOK_spec (hgs u hu)).2 h1
    refine ⟨e1, nv xg u * g, mul_mem (Subgroup.subset_closure ⟨u, hu, rfl⟩) hg, ?_⟩
    rw [idx_mul, hge]
    exact e2.symm

theorem orbit_card {l : ℕ} (hl : l < 7) :
    (nthL J.orb l).length ≤ Nat.card (MulAction.orbit (Hl l) (bpt l)) := by
  obtain ⟨h1, S, hS, hSr⟩ := orbOK_spec_ (orb_len_le hl) (bAll l (show l < 7 by omega))
  have hgs : ∀ g ∈ nthL J.gens l, nwOK g = true := fun g hg => (h1 g hg).1
  have hmem : ∀ a (ha : a ∈ S), (⟨opt J.OP a, oFacts.1 a (hSr a ha).1⟩ : Fin 306936) ∈
      MulAction.orbit (Hl l) (bpt l) := by
    intro a ha
    obtain ⟨-, g, hg, hge⟩ := reach hL hgs (nth_B_lt hl) (hSr a ha).2
    refine ⟨⟨g, hg⟩, Fin.ext ?_⟩
    change ((⟨g, hg⟩ : Hl l) • bpt l).val = opt J.OP a
    rw [Subgroup.smul_def, smul_val, bpt_val hl, hge]
  let f : S → MulAction.orbit (Hl l) (bpt l) := fun a =>
    ⟨⟨opt J.OP a.1, oFacts.1 a.1 (hSr a.1 a.2).1⟩, hmem a.1 a.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have : opt J.OP a.1 = opt J.OP b.1 := congrArg (fun z => z.1.val) hab
    exact Subtype.ext (oFacts.2 _ (hSr a.1 a.2).1 _ (hSr b.1 b.2).1 this)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, hS] at this

@[expose] noncomputable def Hl' (l : ℕ) : Subgroup CFSG.Sporadic.Fi24.J := if l < 7 then Hl l else ⊥

theorem card_P : Nat.card (Nsub xg 0) = 3 ^ 16 ∧ Nat.card (stabN (Nsub xg 0) bpt 7) = 1 := by
  have hc := card_chain (Nsub xg 0) bpt Hl' (fun l => by unfold Hl'; split_ifs; exact Hl_le l; exact bot_le)
    (fun l g hg m hm => by
      unfold Hl' at hg
      split_ifs at hg with h7
      · exact gens_fix hL h7 g hg m hm
      · rw [Subgroup.mem_bot] at hg; rw [hg, one_smul]) 7
  have hprod : 3 ^ 16 ≤ ∏ l ∈ Finset.range 7, Nat.card (MulAction.orbit (Hl' l) (bpt l)) := by
    have o : ∀ l < 7, (nthL J.orb l).length ≤ Nat.card (MulAction.orbit (Hl' l) (bpt l)) := by
      intro l hl
      unfold Hl'
      rw [if_pos hl]
      exact orbit_card hL hl
    obtain ⟨l0, l1, l2, l3, l4, l5, l6⟩ := orb_lens
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul
      (Nat.mul_le_mul (o 0 (by norm_num)) (o 1 (by norm_num))) (o 2 (by norm_num))) (o 3 (by norm_num)))
      (o 4 (by norm_num))) (o 5 (by norm_num))) (o 6 (by norm_num))
    rw [l0, l1, l2, l3, l4, l5, l6] at this
    norm_num at this ⊢
    exact this
  have hle := card_le (pres hL)
  have hs : 0 < Nat.card (stabN (Nsub xg 0) bpt 7) := Nat.card_pos
  have h1 := le_trans (Nat.mul_le_mul_right (Nat.card (stabN (Nsub xg 0) bpt 7)) hprod) hc
  have h2 : 3 ^ 16 * Nat.card (stabN (Nsub xg 0) bpt 7) ≤ 3 ^ 16 * 1 := by omega
  have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
  refine ⟨by omega, by omega⟩

theorem eq_of_base0 {u v : CFSG.Sporadic.Fi24.J} (hu : u ∈ Nsub xg 0) (hv : v ∈ Nsub xg 0)
    (h : ∀ m < 7, idx 306936 u (opt J.OP (nth J.B m)) = idx 306936 v (opt J.OP (nth J.B m))) : u = v := by
  have hmem : v⁻¹ * u ∈ stabN (Nsub xg 0) bpt 7 := ⟨mul_mem (inv_mem hv) hu, fun m hm => Fin.ext (by
    rw [smul_val, bpt_val hm, idx_mul, h m hm, idx_inv_idx])⟩
  have hbot := (Subgroup.card_eq_one).1 (card_P hL).2
  rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
  exact hmem.symm

omit hL in
theorem B_len : J.B.length = 7 := by
  have := sck_ok
  unfold sck at this
  rw [andB_eq, Bool.and_eq_true, beq_iff, lenL_eq] at this
  exact this.1

omit hL in
theorem nth_mem {B : List ℕ} {m : ℕ} (hm : m < B.length) : nth B m ∈ B := by
  rw [← getElem!_nth, getElem!_pos B m hm]
  exact List.getElem_mem hm

theorem eqO_prod {l₁ l₂ : List ℕ} (h₁ : ∀ w ∈ l₁, ∀ k, dg w k < 3) (h₂ : ∀ w ∈ l₂, ∀ k, dg w k < 3)
    (h : eqO J.TB J.B l₁ l₂ = true) : (l₁.map (nv xg)).prod = (l₂.map (nv xg)).prod := by
  have hP : ∀ l : List ℕ, (l.map (nv xg)).prod ∈ Nsub xg 0 := fun l =>
    (Nsub xg 0).list_prod_mem fun (g : CFSG.Sporadic.Fi24.J) hg => by
      obtain ⟨u, -, rfl⟩ := List.mem_map.1 hg
      exact nv_mem fun _ h => absurd h (Nat.not_lt_zero _)
  apply eq_of_base0 hL (hP _) (hP _)
  intro m hm
  have hb := nth_B_lt hm
  have e := eqO_spec h _ (nth_mem (by rw [B_len]; exact hm))
  have e1 := (evW_spec actJ (fun g h p => idx_mul g h p) (fun p => idx_one p) (tabF hL) h₁ hb).2
  have e2 := (evW_spec actJ (fun g h p => idx_mul g h p) (fun p => idx_one p) (tabF hL) h₂ hb).2
  rw [e] at e1
  exact e1.symm.trans e2

omit hL in
theorem dg_gw (i k : ℕ) (hi : i < 16) : dg (gw i) k < 3 := by
  rw [gw_eq, show 4 ^ i = 0 + 1 * 4 ^ i by ring]
  rcases lt_trichotomy k i with h | rfl | h
  · rw [dg_add_lt h]; simp [dg]
  · rw [dg_add_self (by positivity) (by norm_num)]; norm_num
  · rw [dg_add_gt (by positivity) (by norm_num) h]; norm_num

omit hL in
theorem nv_gw {i : ℕ} (hi : i < 16) : nv xg (gw i) = xg i := by
  rw [gw_eq, show 4 ^ i = 0 + 1 * 4 ^ i by ring, nv_add hi (by positivity) (by norm_num), nv_zero,
    one_mul, pow_one]

omit hL in
theorem kids_facts {i : ℕ} (hi : i < 16) :
    (∀ y ∈ nthL J.levels i, nwOK y = true ∧ y < 4 ^ i) ∧
      (nthL J.levels i).length = (nthL J.tags i).length ∧
      nthL J.levels (i + 1) = kidsL i (nthL J.levels i) (nthL J.tags i) :=
  kidsOK_spec (kAll i (show i < 16 by omega))

omit hL in
theorem sck_parts : (nthL J.levels 16).length = J.fin.length ∧ nthL J.levels 0 = [0] ∧
    (nthL J.levels 16).length ≤ 1088 ∧ ∀ i < 16, (nthL J.levels i).length ≤ 2048 := by
  have := sck_ok
  unfold sck at this
  simp only [andB_eq, Bool.and_eq_true, beq_iff, lenL_eq] at this
  refine ⟨this.2.1, eqL_spec this.2.2.1, ?_, fun i hi => ?_⟩
  · have := blt_iff.1 this.2.2.2.1; omega
  · have h := CFSG.KC.Fi24FixS.allBelow_spec this.2.2.2.2.1 (by norm_num) i hi
    rw [blt_iff] at h
    omega

omit hL in
theorem rep_all {i : ℕ} (hi : i < 16) : ∀ j < (nthL J.levels i).length,
    repOK J.TB J.B i ((nthL J.levels i)[j]!) ((nthL J.tags i)[j]!) = true := by
  intro j hj
  refine repsOK_slices (sck_parts.2.2.2 i hi) (fun s hs => ?_) j hj
    (by rw [← (kids_facts hi).2.1]; exact hj)
  have := pAll (32 * i + s) (show 32 * i + s < 512 by omega)
  unfold pck at this
  rwa [show Nat.div (32 * i + s) 32 = i by change (32 * i + s) / 32 = i; omega,
    show Nat.mod (32 * i + s) 32 = s by change (32 * i + s) % 32 = s; omega] at this

theorem classCert : ClassCert xg (fun i => nthL J.levels i) (fun i => nthL J.tags i) := by
  refine ⟨sck_parts.2.1, fun i hi y hy => ((kids_facts hi).1 y hy).2, fun i hi => (kids_facts hi).2.1,
    fun i hi => (kids_facts hi).2.2, fun i hi j hj => ?_⟩
  obtain ⟨r0, r1, r3⟩ := repOK_spec (rep_all hi j hj)
  have hy := ((kids_facts hi).1 ((nthL J.levels i)[j]!)
    (by rw [getElem!_pos (nthL J.levels i) j hj]; exact List.getElem_mem hj)).1
  have hyd := (nwOK_spec hy).2
  generalize (nthL J.levels i)[j]! = y at *
  generalize (nthL J.tags i)[j]! = g at *
  refine ⟨fun t0 => ?_, fun t1 => ?_, r3⟩
  · obtain ⟨a1, a2, a3⟩ := r0 t0
    generalize g / 4 % 2 ^ 32 = a at *
    have had := (nwOK_spec a1).2
    refine ⟨(nwOK_spec a1).1, had, ?_, ?_⟩
    · by_contra hne
      exact a2 (land_lowM_eq_zero.2 fun k hk => by
        by_contra h0
        exact hne ⟨k, hk, h0⟩)
    · have := eqO_prod hL (l₁ := [y, y, y]) (l₂ := [a])
        (fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hyd
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hyd
          rcases List.mem_cons.1 hw with rfl | hw
          · exact hyd
          · exact absurd hw List.not_mem_nil)
        (fun w hw => by
          rcases List.mem_cons.1 hw with rfl | hw
          · exact had
          · exact absurd hw List.not_mem_nil) a3
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
      rw [← this, pow_succ, pow_two, mul_assoc]
  · obtain ⟨a1, b1, b2, a3⟩ := r1 t1
    generalize g / 4 % 2 ^ 32 = a at *
    generalize g / 2 ^ 34 = b at *
    have had := (nwOK_spec a1).2
    have hbd := (nwOK_spec b1).2
    refine ⟨fun k hk => land_lowM_eq_zero.1 b2 k (by omega), ?_⟩
    have := eqO_prod hL (l₁ := [a, y]) (l₂ := [y, gw i, a, b])
      (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact had
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hyd
        · exact absurd hw List.not_mem_nil)
      (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hyd
        rcases List.mem_cons.1 hw with rfl | hw
        · exact fun k => dg_gw i k hi
        rcases List.mem_cons.1 hw with rfl | hw
        · exact had
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hbd
        · exact absurd hw List.not_mem_nil) a3
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, nv_gw hi] at this
    rw [this]
    group

omit hL in
theorem tw_eq {k : ℕ} (hk : k < 5) : nthL J.tw k = repWords ⟨k, hk⟩ := by
  have h := twck_ok
  unfold twck at h
  simp only [andB_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl
  · exact eqL_spec h0
  · exact eqL_spec h1
  · exact eqL_spec h2
  · exact eqL_spec h3
  · exact eqL_spec h4

theorem trans_conj {l : ℕ} (hl : l < 824) : (∀ k, dg (f32 J.RP l) k < 3) ∧
    ∃ i : Fin 5, wordElt (nthL J.trans l) * nv xg (f32 J.RP l) * (wordElt (nthL J.trans l))⁻¹ =
      fi24Rep3 i := by
  have hx := xchunk_spec (xAll (l / 8) (show l / 8 < 103 by omega)) (l % 8) (Nat.mod_lt _ (by norm_num))
    (by omega)
  rw [show 8 * (l / 8) + l % 8 = l by omega] at hx
  unfold xone at hx
  rw [bAnd_eq, Bool.and_eq_true, blt_iff] at hx
  obtain ⟨ht, hT⟩ := hx
  obtain ⟨hr, hb⟩ := transOK_spec hT
  have hrd := (nwOK_spec hr).2
  refine ⟨hrd, ⟨nth J.tgt l, ht⟩, ?_⟩
  have hw := lck_spec.2.2 (nth J.tgt l)
  have htl := lck_spec.2.1 l
  have e : wordElt (nthL J.tw (nth J.tgt l)) * wordElt (nthL J.trans l) =
      wordElt (nthL J.trans l) * nv xg (f32 J.RP l) := by
    apply eq_of_cb
    intro b hb'
    have e1 := hb b hb'
    have hbl := cb_lt b hb'
    have lN : letN CFSG.KD.Fi24Net.NW = LN CFSG.KD.Fi24Net.NW := funext fun l => funext fun x => letN_eq _ l x
    rw [lN, nwL_idx hL hrd hbl, ← idx_wordElt hL _ htl _ hbl,
      ← idx_wordElt hL _ htl _ (idx_lt _ hbl), ← idx_wordElt hL _ hw _ (idx_lt _ hbl)] at e1
    rw [idx_mul, idx_mul]
    exact e1
  unfold fi24Rep3
  rw [← tw_eq ht, ← e]
  group

omit hL in
theorem factorization_three (k m : ℕ) (hm : ¬ 3 ∣ m) : (3 ^ k * m).factorization 3 = k := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem fi24ThreeClasses_of_letters : Fi24ThreeClasses := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcP, -⟩ := card_P hL
  have hcard : Nat.card (Nsub xg 0) = 3 ^ (Nat.card CFSG.Sporadic.Fi24.J).factorization 3 := by
    rw [hcP, CFSG.Sporadic.Fi24.card_J,
      show (1255205709190661721292800 : ℕ) = 3 ^ 16 * 29159148014796800 by norm_num,
      factorization_three 16 _ (by norm_num)]
  let T : Sylow 3 CFSG.Sporadic.Fi24.J := Sylow.ofCard (Nsub xg 0) hcard
  intro s hs
  have hsp : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq CFSG.Sporadic.Fi24.J Q T
  have hsT : g * s * g⁻¹ ∈ Nsub xg 0 := by
    have h1 : s ∈ (Q : Subgroup CFSG.Sporadic.Fi24.J) := hQ (Subgroup.mem_zpowers s)
    have h2 : MulAut.conj g s ∈ (MulAut.conj g • (Q : Set CFSG.Sporadic.Fi24.J)) := Set.smul_mem_smul_set h1
    rw [← Sylow.coe_smul, hg] at h2
    have h3 : g * s * g⁻¹ ∈ T := by simpa [MulAut.conj_apply] using h2
    have h4 : g * s * g⁻¹ ∈ (T : Subgroup CFSG.Sporadic.Fi24.J) := h3
    rwa [Sylow.coe_ofCard] at h4
  have hs3 : s ^ 3 = 1 := by have := pow_orderOf_eq_one s; rwa [hs] at this
  have h3 : (g * s * g⁻¹) ^ 3 = 1 := by
    have e : (g * s * g⁻¹) ^ 3 = g * s ^ 3 * g⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_mul_cancel_left]
    rw [e, hs3, mul_one, mul_inv_cancel]
  obtain ⟨y, hy, c, hc, hcy⟩ := cover (pres hL) (by omega) (classCert hL) hsT h3
  obtain ⟨m, hm, hym⟩ := List.getElem_of_mem hy
  have hmF : m < J.fin.length := by rw [← sck_parts.1]; exact hm
  have hfin := finsOK_slices sck_parts.2.2.1 (fun s hs => fAll s (show s < 17 by omega)) m hm hmF
  rw [getElem!_pos _ m hm, hym] at hfin
  obtain ⟨f0, f1, f2⟩ := finOK_spec hfin
  generalize J.fin[m]! = f at f0 f1 f2
  have hyd : ∀ k, dg y k < 3 := by
    have hk := (kids_facts (i := 15) (by norm_num)).2.2
    have hmem : y ∈ kidsL 15 (nthL J.levels 15) (nthL J.tags 15) := by
      rw [← hk]; exact hy
    obtain ⟨y', hy', e, he, hz⟩ := kidsL_inv hmem
    have hk15 := (kids_facts (i := 15) (by norm_num)).1 y' hy'
    rw [hz]
    exact dg_kid hk15.2 (nwOK_spec hk15.1).2 he
  have hcube : (nv xg y) ^ 3 = 1 := by
    have e : (c * (g * s * g⁻¹) * c⁻¹) ^ 3 = c * (g * s * g⁻¹) ^ 3 * c⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, inv_mul_cancel_left]
    rw [← hcy, e, h3, mul_one, mul_inv_cancel]
  by_cases t0 : f % 4 = 0
  · exfalso
    rw [f0 t0, nv_zero] at hcy
    have : s = 1 := by
      have := congrArg (fun z => (c * g)⁻¹ * z * (c * g)) hcy
      rw [show (c * g)⁻¹ * (c * (g * s * g⁻¹) * c⁻¹) * (c * g) = s by group] at this
      rw [this]; group
    rw [this, orderOf_one] at hs
    exact absurd hs (by norm_num)
  by_cases t1 : f % 4 = 1
  · exfalso
    obtain ⟨a1, a2, a3⟩ := f1 t1
    have := eqO_prod hL (l₁ := [_, _, _]) (l₂ := [f / 4 % 2 ^ 32])
      (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hyd
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hyd
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hyd
        · exact absurd hw List.not_mem_nil)
      (fun w hw => by
        rcases List.mem_cons.1 hw with rfl | hw
        · exact (nwOK_spec a1).2
        · exact absurd hw List.not_mem_nil) a3
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    rw [← mul_assoc, ← pow_two, ← pow_succ, hcube] at this
    have hmem : nv xg (f / 4 % 2 ^ 32) ∈ Nsub xg 16 := by rw [← this]; exact one_mem _
    have hz := dg_zero (pres hL) (by omega) (nwOK_spec a1).1 (nwOK_spec a1).2 hmem
    have := (mod_four_pow_eq_zero 16 _).2 hz
    rw [Nat.mod_eq_of_lt (nwOK_spec a1).1] at this
    exact a2 this
  obtain ⟨-, hl, hd, a3⟩ := f2 t0 t1
  obtain ⟨hrd, i, hi⟩ := trans_conj hL hl
  have := eqO_prod hL (l₁ := [f / 2 ^ 34, y]) (l₂ := [f32 J.RP (f / 4 % 2 ^ 32), f / 2 ^ 34])
    (fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw
      · exact (nwOK_spec hd).2
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hyd
      · exact absurd hw List.not_mem_nil)
    (fun w hw => by
      rcases List.mem_cons.1 hw with rfl | hw
      · exact hrd
      rcases List.mem_cons.1 hw with rfl | hw
      · exact (nwOK_spec hd).2
      · exact absurd hw List.not_mem_nil) a3
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  refine ⟨i, isConj_iff.2 ⟨wordElt (nthL J.trans (f / 4 % 2 ^ 32)) * nv xg (f / 2 ^ 34) * c * g, ?_⟩⟩
  rw [← hi]
  have e1 : nv xg (f32 J.RP (f / 4 % 2 ^ 32)) =
      nv xg (f / 2 ^ 34) * nv xg y * (nv xg (f / 2 ^ 34))⁻¹ := by
    rw [this]; group
  rw [e1, ← hcy]
  group

end J

end CFSG.KD.Fi24Pc

end
