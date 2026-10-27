module

public import Certificates.Kernel.Fi23C.Checks
public import Certificates.Kernel.Fi23C.Rows
public import Certificates.Data.CFSGNative.Fi23.Centralizer
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23C

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23C CFSG.KS.Raw.Orb
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.KS.PK

noncomputable abbrev E (i : Nat) : Nat := tb H 0 i
noncomputable abbrev P (x : Nat) : Nat := tb H 1 x
noncomputable abbrev Φ (i : Nat) : Nat := tb H 2 i
noncomputable abbrev ΦI (u : Nat) : Nat := tb H 3 u

theorem ea_facts : (∀ i < 3510, 0 < E i ∧ E i < 31671 ∧ tb G 43 (E i) = E i ∧ P (E i) = i) ∧
    ∀ i < 3509, E i < E (i + 1) := by
  have h := ea_ok
  unfold eaK at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · have h1 := allN_iff.1 h.1 i hi
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    exact h1
  · have h2 := allN_iff.1 h.2 i hi
    simpa [Nat.blt_eq] using h2

theorem ep_facts {x : Nat} (hx : x < 31671) :
    (P x < 3510 ∧ E (P x) = x) ∨ (P x = 3510 ∧ (x = 0 ∨ tb G 43 x ≠ x)) := by
  have h := allN_iff.1 ep_ok x hx
  rw [strictB_eq, bIf_eq] at h
  by_cases hm : P x < 3510
  · rw [if_pos (Nat.blt_eq.mpr hm)] at h
    exact Or.inl ⟨hm, Nat.eq_of_beq_eq_true h⟩
  · rw [if_neg (fun hb => hm (Nat.blt_eq.mp hb)), bAnd_eq, Bool.and_eq_true, bIf_eq] at h
    refine Or.inr ⟨Nat.eq_of_beq_eq_true h.1, ?_⟩
    by_cases h0 : x = 0
    · exact Or.inl h0
    · rw [if_neg (fun hb => h0 (Nat.eq_of_beq_eq_true hb))] at h
      right
      intro e
      rw [e, Nat.beq_refl] at h
      exact absurd h.2 (by decide)

theorem E_mono {i j : Nat} (hij : i < j) (hj : j < 3510) : E i < E j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans (ea_facts.2 j (by omega))
    · exact ea_facts.2 i (by omega)

theorem E_lt {i : Nat} (hi : i < 3510) : E i < 31671 := (ea_facts.1 i hi).2.1
theorem E_ne {i : Nat} (hi : i < 3510) : E i ≠ 0 := by have := (ea_facts.1 i hi).1; omega
theorem E_fix {i : Nat} (hi : i < 3510) : tb G 43 (E i) = E i := (ea_facts.1 i hi).2.2.1
theorem P_E {i : Nat} (hi : i < 3510) : P (E i) = i := (ea_facts.1 i hi).2.2.2

theorem E_inj {i j : Nat} (hi : i < 3510) (hj : j < 3510) (h : E i = E j) : i = j := by
  rw [← P_E hi, ← P_E hj, h]

@[expose] noncomputable def EL : List Nat := (List.range 3510).map E

theorem EL_pairwise : EL.Pairwise (· < ·) := by
  unfold EL
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro i j _ hj hij
  exact E_mono hij (List.mem_range.1 hj)

theorem mem_star {D : Table} (hD : ∀ k < 31671, ap D k = tb G 43 k) {x : Nat} :
    (x < 31671 ∧ x ≠ 0 ∧ ap D x = x) ↔ x ∈ EL := by
  constructor
  · rintro ⟨hx, hx0, hxa⟩
    rw [hD x hx] at hxa
    rcases ep_facts hx with ⟨hm, he⟩ | ⟨-, h0 | h0⟩
    · exact List.mem_map.2 ⟨P x, List.mem_range.2 hm, he⟩
    · exact absurd h0 hx0
    · exact absurd hxa h0
  · intro hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have hi' := List.mem_range.1 hi
    exact ⟨E_lt hi', E_ne hi', by rw [hD _ (E_lt hi')]; exact E_fix hi'⟩

theorem starPts_toList {D : Table} (hD : ∀ k < 31671, ap D k = tb G 43 k) :
    (starPts D).toList = EL := by
  unfold starPts
  rw [List.toList_toArray]
  refine List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _) EL_pairwise fun x => ?_
  rw [List.mem_filter, List.mem_range, ← mem_star hD]
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]

theorem starPts_size {D : Table} (hD : ∀ k < 31671, ap D k = tb G 43 k) :
    (starPts D).size = 3510 := by
  rw [← Array.length_toList, starPts_toList hD, EL, List.length_map, List.length_range]

theorem starPts_get {D : Table} (hD : ∀ k < 31671, ap D k = tb G 43 k) {i : Nat} (hi : i < 3510) :
    (starPts D)[i]! = E i := by
  rw [getElem!_pos _ i (by rw [starPts_size hD]; exact hi), ← Array.getElem_toList]
  simp only [starPts_toList hD, EL, List.getElem_map, List.getElem_range]

theorem starPos_get {D : Table} (hD : ∀ k < 31671, ap D k = tb G 43 k) {x : Nat} (hx : x ∈ EL) :
    (starPos (starPts D))[x]! = P x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hi' := List.mem_range.1 hi
  unfold starPos
  rw [getElem!_pos _ _ (by simpa using E_lt hi'), Array.getElem_ofFn, starPts_toList hD]
  simp only
  have hnd : EL.Nodup := EL_pairwise.imp ne_of_lt
  have hl : i < EL.length := by simp [EL, hi']
  have e1 : EL[i] = E i := by simp [EL]
  have := List.get_idxOf hnd ⟨i, hl⟩
  simp only [List.get_eq_getElem, e1] at this
  rw [this, P_E hi']

theorem mem_EL {i : Nat} (hi : i < 3510) : E i ∈ EL :=
  List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

theorem phi_facts {i : Nat} (hi : i < 3510) : Φ i < 3510 ∧ ΦI i < 3510 ∧ ΦI (Φ i) = i ∧
    Φ (ΦI i) = i := by
  have h := allN_iff.1 phi_ok i hi
  simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem hList_length (r : Nat) : ∀ c j, (hList H r j c).length = c
  | 0, _ => rfl
  | c + 1, j => by simp only [hList, List.length_cons, hList_length r c (j + 1)]

theorem hList_getElem (r : Nat) : ∀ c j i (h : i < (hList H r j c).length),
    (hList H r j c)[i] = tb H r (j + i)
  | 0, _, _, h => absurd h (by simp [hList])
  | c + 1, j, 0, _ => by simp [hList]
  | c + 1, j, i + 1, h => by
    simp only [hList, List.getElem_cons_succ]
    rw [hList_getElem r c (j + 1) i]
    congr 1
    omega

theorem digs_facts : ∀ f n, n < 10 ^ f → 0 < f →
    digs f n ≠ [] ∧ (∀ c ∈ digs f n, 48 ≤ c ∧ c ≤ 57) ∧ decVal (digs f n) = n
  | 0, _, _, h => absurd h (lt_irrefl 0)
  | f + 1, n, hn, _ => by
    by_cases h10 : n < 10
    · have e : digs (f + 1) n = [48 + n] := by simp [digs, h10]
      rw [e]
      refine ⟨by simp, fun c hc => ?_, ?_⟩
      · rw [List.mem_singleton] at hc
        omega
      · simp [decVal]
    · have e : digs (f + 1) n = digs f (n / 10) ++ [48 + n % 10] := by simp [digs, h10]
      rw [e]
      have hf : 0 < f := by
        rcases Nat.eq_zero_or_pos f with rfl | h
        · simp at hn
          omega
        · exact h
      have hn' : n / 10 < 10 ^ f := by
        rw [pow_succ] at hn
        omega
      obtain ⟨h1, h2, h3⟩ := digs_facts f (n / 10) hn' hf
      refine ⟨by simp, fun c hc => ?_, ?_⟩
      · rcases List.mem_append.1 hc with hc | hc
        · exact h2 c hc
        · rw [List.mem_singleton] at hc
          omega
      · unfold decVal at h3 ⊢
        rw [List.foldl_append, h3]
        simp only [List.foldl_cons, List.foldl_nil]
        omega

theorem splitOn_render : ∀ L : List Nat, L ≠ [] → (∀ n ∈ L, n < 10 ^ 6) →
    (render L).splitOn 32 = L.map (digs 6)
  | [], h, _ => absurd rfl h
  | [n], _, hL => by
    have hd := digs_facts 6 n (hL n (by simp)) (by norm_num)
    rw [render, List.map_singleton]
    refine List.splitOn_eq_singleton fun h => ?_
    have := hd.2.1 _ h
    omega
  | n :: m :: l, _, hL => by
    have hd := digs_facts 6 n (hL n (by simp)) (by norm_num)
    rw [render, List.splitOn_append_cons_self_of_not_mem, splitOn_render (m :: l) (by simp)
      (fun k hk => hL k (List.mem_cons_of_mem _ hk))]
    · simp
    · intro h
      have := hd.2.1 _ h
      omega

theorem render_lt : ∀ L : List Nat, (∀ n ∈ L, n < 10 ^ 6) → ∀ c ∈ render L, c < 128
  | [], _ => by simp [render]
  | [n], hL => by
    intro c hc
    have hd := digs_facts 6 n (hL n (by simp)) (by norm_num)
    rw [render] at hc
    have := hd.2.1 c hc
    omega
  | n :: m :: l, hL => by
    intro c hc
    have hd := digs_facts 6 n (hL n (by simp)) (by norm_num)
    rw [render] at hc
    rcases List.mem_append.1 hc with hc | hc
    · have := hd.2.1 c hc
      omega
    · rcases List.mem_cons.1 hc with rfl | hc
      · omega
      · exact render_lt (m :: l) (fun k hk => hL k (List.mem_cons_of_mem _ hk)) c hc

theorem natsOf_render (L : List Nat) (hne : L ≠ []) (hL : ∀ n ∈ L, n < 10 ^ 6) :
    natsOf (strL (render L)) = L.toArray := by
  unfold natsOf
  rw [splitOn_space_strL (render_lt L hL), splitOn_render L hne hL, List.map_map]
  have hf : (L.map (strL ∘ digs 6)).filter (· != "") = L.map (strL ∘ digs 6) := by
    rw [List.filter_eq_self]
    intro s hs
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hs
    have hd := digs_facts 6 n (hL n hn) (by norm_num)
    simp only [Function.comp_apply, bne_iff_ne, ne_eq]
    rw [strL_eq_empty_iff]
    exact hd.1
  rw [hf, List.map_toArray, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_id L]
  refine List.map_congr_left fun n hn => ?_
  have hd := digs_facts 6 n (hL n hn) (by norm_num)
  simp only [Function.comp_apply, id_eq]
  rw [toNat!_strL ⟨hd.1, hd.2.1⟩, hd.2.2]

theorem phiList_lt : ∀ n ∈ hList H 2 0 3510, n < 10 ^ 6 := by
  intro n hn
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hn
  rw [hList_getElem]
  have hi' : i < 3510 := by rwa [hList_length] at hi
  rw [Nat.zero_add]
  exact lt_of_lt_of_le (phi_facts hi').1 (by norm_num)

theorem starPhi_eq : starPhi () = (hList H 2 0 3510).toArray := by
  rw [lit_ok]
  exact natsOf_render _ (by
    intro h
    have := hList_length 2 3510 0
    rw [h] at this
    simp at this) phiList_lt

theorem starPhi_size : (starPhi ()).size = 3510 := by
  rw [starPhi_eq, List.size_toArray, hList_length]

theorem starPhi_get {i : Nat} (hi : i < 3510) : (starPhi ())[i]! = Φ i := by
  rw [starPhi_eq, getElem!_pos _ i (by rw [List.size_toArray, hList_length]; exact hi)]
  simp only [List.getElem_toArray]
  rw [hList_getElem, Nat.zero_add]

theorem starPhiPos_get {u : Nat} (hu : u < 3510) : (starPhiPos ())[u]! = ΦI u := by
  unfold starPhiPos
  rw [getElem!_pos _ u (by simpa using hu), Array.getElem_ofFn]
  simp only
  rw [starPhi_eq, List.toList_toArray]
  have hlen := hList_length 2 3510 0
  have hget : ∀ i (hi : i < (hList H 2 0 3510).length), (hList H 2 0 3510)[i] = Φ i := by
    intro i hi
    rw [hList_getElem, Nat.zero_add]
  have hnd : (hList H 2 0 3510).Nodup := by
    rw [List.nodup_iff_injective_get]
    intro a b e
    simp only [List.get_eq_getElem, hget] at e
    have ha : a.val < 3510 := lt_of_lt_of_eq a.isLt hlen
    have hb : b.val < 3510 := lt_of_lt_of_eq b.isLt hlen
    apply Fin.ext
    rw [← (phi_facts ha).2.2.1, ← (phi_facts hb).2.2.1, e]
  have hp := phi_facts hu
  have hl : ΦI u < (hList H 2 0 3510).length := by rw [hlen]; exact hp.2.1
  have e1 : (hList H 2 0 3510)[ΦI u] = u := by rw [hget _ hl, hp.2.2.2]
  have := List.get_idxOf hnd ⟨ΦI u, hl⟩
  simp only [List.get_eq_getElem, e1] at this
  exact this

theorem uF_succ (f k y : Nat) : uF G (f + 1) k y =
    if k = 0 then y else (if tb G 92 k = 1 then tb G 39 else tb G 40) (uF G f (tb G 91 k) y) := by
  change nIf(Nat.beq k 0, y, strictN (uF G f (tb G 91 k) y) fun z =>
    nIf(Nat.beq (tb G 92 k) 1, tb G 39 z, tb G 40 z)) = _
  rw [strictN_eq]
  by_cases h0 : k = 0
  · subst h0
    rfl
  · rw [if_neg h0]
    have e : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun hb => h0 (Nat.eq_of_beq_eq_true hb)
    rw [e]
    by_cases hl : tb G 92 k = 1
    · rw [if_pos hl, hl]
      rfl
    · rw [if_neg hl]
      have e2 : Nat.beq (tb G 92 k) 1 = false :=
        Bool.eq_false_iff.2 fun hb => hl (Nat.eq_of_beq_eq_true hb)
      rw [e2]

theorem uInvF_succ (f k x : Nat) : uInvF G (f + 1) k x =
    if k = 0 then x else uInvF G f (tb G 91 k) (if tb G 92 k = 1 then tb G 39 x else tb G 41 x) := by
  change nIf(Nat.beq k 0, x, uInvF G f (tb G 91 k)
    (nIf(Nat.beq (tb G 92 k) 1, tb G 39 x, tb G 41 x))) = _
  by_cases h0 : k = 0
  · subst h0
    rfl
  · rw [if_neg h0]
    have e : Nat.beq k 0 = false := Bool.eq_false_iff.2 fun hb => h0 (Nat.eq_of_beq_eq_true hb)
    rw [e]
    by_cases hl : tb G 92 k = 1
    · rw [if_pos hl, hl]
      rfl
    · rw [if_neg hl]
      have e2 : Nat.beq (tb G 92 k) 1 = false :=
        Bool.eq_false_iff.2 fun hb => hl (Nat.eq_of_beq_eq_true hb)
      rw [e2]

theorem cJ_eq (k x : Nat) : cJ G k x = uF G 31671 k (tb G 43 (uInvF G 31671 k x)) := by
  unfold cJ
  rw [strictN_eq]

noncomputable abbrev GS (s : Nat) : Nat := tb H 8 s

theorem rs_all : ∀ s < 7, rs s = true := by
  intro s hs
  interval_cases s
  exacts [rs0, rs1, rs2, rs3, rs4, rs5, rs6]

theorem row_facts {s j : Nat} (hs : s < 7) (hj : j < 3510) :
    GS s < 3510 ∧ P (cJ G (E (GS s)) (E j)) < 3510 ∧
      E (P (cJ G (E (GS s)) (E j))) = cJ G (E (GS s)) (E j) ∧
      Φ (P (cJ G (E (GS s)) (E j))) = CFSG.KS.Fi22Cent.cK (Φ (GS s)) (Φ j) := by
  have hr := rs_all s hs
  unfold rs rowSl at hr
  have h := allN_iff.1 hr j hj
  unfold rowAt at h
  simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact h

noncomputable abbrev ORK (t : Nat) : Nat := tb H 4 t
noncomputable abbrev OIK (i : Nat) : Nat := tb H 5 i
noncomputable abbrev TP (t : Nat) : Nat := tb H 6 t
noncomputable abbrev TG (t : Nat) : Nat := tb H 7 t

theorem tree_facts : ORK 0 = GS 0 ∧
    (∀ t < 3510, ORK t < 3510 ∧ (0 < t → TP t < t ∧ TG t < 7 ∧
      cJ G (E (GS (TG t))) (E (ORK (TP t))) = E (ORK t))) ∧
    ∀ i < 3510, OIK i < 3510 ∧ ORK (OIK i) = i := by
  have h := tree_ok
  unfold CFSG.KC.Fi23C.treeK at h
  rw [bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h0, fun t ht => ?_, fun i hi => ?_⟩
  · have h := allN_iff.1 h1 t ht
    rw [bAnd_eq, Bool.and_eq_true, bIf_eq] at h
    refine ⟨Nat.blt_eq.mp h.1, fun ht0 => ?_⟩
    have h' := h.2
    rw [if_neg (fun hb => absurd (Nat.eq_of_beq_eq_true hb) (Nat.pos_iff_ne_zero.mp ht0))] at h'
    simp only [strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h'
    exact h'
  · have h := allN_iff.1 h2 i hi
    simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
    exact h

theorem swK_spec : ∀ w, swK H w = true → ∀ k ∈ w, P k < 3510 ∧ E (P k) = k
  | [], _, k, hk => absurd hk (by simp)
  | a :: w, h, k, hk => by
    have e : swK H (a :: w) = bAnd(Nat.blt (tb H 1 a) 3510, bAnd(Nat.beq (tb H 0 (tb H 1 a)) a,
        swK H w)) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true, bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2.1⟩
    · exact swK_spec w h.2.2 k hk

theorem sw_facts : ∀ k ∈ starWord, P k < 3510 ∧ E (P k) = k := swK_spec _ sw_ok

theorem powK_spec {w : List Nat} {m : Nat} : ∀ Q, powK G w m Q = true →
    ∀ q ∈ Q, CFSG.KS.Fi22Cent.itK (wordJ G w) m q = tb G 43 q
  | [], _, q, hq => absurd hq (by simp)
  | a :: Q, h, q, hq => by
    have e : powK G w m (a :: Q) = bAnd(Nat.beq (CFSG.KS.Fi22Cent.itK (wordJ G w) m a) (tb G 43 a),
        powK G w m Q) := rfl
    rw [e, bAnd_eq, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Nat.eq_of_beq_eq_true h.1
    · exact powK_spec Q h.2 q hq

theorem pow_facts : ∀ q < 6, CFSG.KS.Fi22Cent.itK (wordJ G starWord) 11 q = tb G 43 q := by
  intro q hq
  refine powK_spec _ pow_ok q ?_
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  omega

theorem d2_facts {x : Nat} (hx : x < 31671) : tb G 43 (tb G 43 x) = x :=
  Nat.eq_of_beq_eq_true (allN_iff.1 d2_ok x hx)

end CertificateChecks.KernelFi23C

end
