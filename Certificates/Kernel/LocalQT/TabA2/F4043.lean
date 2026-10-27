module

public import Certificates.Kernel.LocalQT.TabA2.C4043
public import Certificates.Kernel.LocalQT.TabA2.C4043S0
public import Certificates.Kernel.LocalQT.TabA2.C4043S1
public import Certificates.Kernel.LocalQT.TabA2.C4043S2
public import Certificates.Kernel.LocalQT.TabA2.C4043S3
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import Std.Tactic.BVDecide.Normalize.Bool

public section

set_option maxRecDepth 400000

#kqb_all CFSG.KD.LQT.TA.S CFSG.KD.LQT.TA.ckS 315

namespace CFSG.KD.LQT.TA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.TabA2
open CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.Tab.A2

@[expose] def P (a : Array Nat) (A : Nat) : Prop :=
  a = unpack 42 6 A ∧ canonK 42 6 (mask 6) (42 * 6) A = true

theorem cn_eq (A : Nat) : cn A = canonK 42 6 (mask 6) (42 * 6) A := rfl

theorem hn : szOK 42 6 = true := by quickRfl

theorem idP : P (idTab 42) idn :=
  ⟨(idK_sound (n := 42) (w := 6) (by quickRfl)).symm, by quickRfl⟩

theorem compP {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    P (comp 42 a b) (pc A B) := by
  rw [ha.1, hb.1]
  exact ⟨CFSG.KC.BfsPin.compA_unpack ha.2 hb.2, CFSG.KC.BfsPin.canonK_pcomp ha.2 hb.2⟩

theorem beqP {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    (a == b) = Nat.beq A B := by
  rw [ha.1, hb.1]
  exact beq_unpack ha.2 hb.2

theorem getP {a : Array Nat} {A : Nat} (ha : P a A) : a[0]! = at0 A := by
  rw [ha.1, unpack, getElem!_pos _ 0 (by simp), Array.getElem_ofFn]
  rfl

theorem invP {a : Array Nat} {A : Nat} (ha : P a A) (h : invOK A (pinv A) = true) :
    P (invTab 42 a) (pinv A) ∧ ((invTab 42 a).size == 42) = true ∧
      (comp 42 (invTab 42 a) a == idTab 42) = true := by
  unfold invOK at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  have e : invTab 42 a = unpack 42 6 (pinv A) := by
    rw [ha.1]
    exact CFSG.KC.BfsPin.invCand_unpack h1
  have hP : P (invTab 42 a) (pinv A) := ⟨e, h2⟩
  refine ⟨hP, ?_, ?_⟩
  · rw [e, unpack_size]
    rfl
  · rw [beqP (compP hP ha) idP]
    exact h3

theorem memU_spec {U : Nat → Nat} {x : Nat} (h : memU U x = true) : ∃ l < 16, U l = x := by
  have key : ∀ n, anyK n (fun l => Nat.beq (U l) x) = true → ∃ l < n, U l = x := by
    intro n
    induction n with
    | zero => intro h; exact absurd h Bool.false_ne_true
    | succ n ih =>
      intro h
      change Bool.rec (motive := fun _ => Bool) (anyK n _) true (Nat.beq (U n) x) = true at h
      cases hb : Nat.beq (U n) x
      · rw [hb] at h
        obtain ⟨l, hl, e⟩ := ih h
        exact ⟨l, by omega, e⟩
      · exact ⟨n, by omega, Nat.eq_of_beq_eq_true hb⟩
  exact key 16 h

theorem anyK_spec {n : Nat} {f : Nat → Bool} (h : anyK n f = true) : ∃ i < n, f i = true := by
  induction n with
  | zero => exact absurd h Bool.false_ne_true
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) (anyK n f) true (f n) = true at h
    cases hb : f n
    · rw [hb] at h
      obtain ⟨l, hl, e⟩ := ih h
      exact ⟨l, by omega, e⟩
    · exact ⟨n, by omega, hb⟩

theorem allBelow_of {m : Nat} {f : Nat → Bool} (h : ∀ i < m, f i = true) : allBelow m f = true := by
  unfold allBelow
  rw [List.all_eq_true]
  intro i hi
  exact h i (List.mem_range.1 hi)

theorem anyBelow_of {m : Nat} {f : Nat → Bool} {i : Nat} (hi : i < m) (h : f i = true) :
    anyBelow m f = true := by
  unfold anyBelow
  rw [List.any_eq_true]
  exact ⟨i, List.mem_range.2 hi, h⟩

theorem allBelow_mem {A : Array Tab} {f : Tab → Bool} (h : ∀ x ∈ A.toList, f x = true) :
    allBelow A.size (fun i => f A[i]!) = true := by
  refine allBelow_of fun i hi => ?_
  rw [getElem!_pos A i hi]
  exact h _ (Array.getElem_mem_toList hi)

theorem anyBelow_mem {A : Array Tab} {f : Tab → Bool} {x : Tab} (hx : x ∈ A.toList)
    (h : f x = true) : anyBelow A.size (fun j => f A[j]!) = true := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx
  have hj' : j < A.size := by simpa using hj
  refine anyBelow_of hj' ?_
  rw [getElem!_pos A j hj']
  simp only [Array.getElem_toList] at e
  rw [e]
  exact h

theorem uSize : uTabs.size = 16 := rfl

theorem bindU : (allN 16 fun j => bindArrK uTabs[j]! 42 6 (U j)) = true := by quickRfl

theorem bindX : (bindArrK a0T 42 6 (X 0) && bindArrK zT 42 6 (X 1) &&
    bindArrK r₂T 42 6 (X 2)) = true := by quickRfl

theorem gensOK : GensOK 42 6 3 S.G gensS := gensOK_of (by quickRfl)

theorem u1 {j : Nat} (hj : j < 16) : cn (U j) = true ∧ W j < S.cnt ∧ S.T (W j) = U j ∧
    at0 (U j) = 0 ∧ pc (U j) (U j) = idn := by
  have h := allN_spec u1_ok j hj
  simp only [bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, h.2.1, Nat.eq_of_beq_eq_true h.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2.2⟩

theorem pU {j : Nat} (hj : j < 16) : P uTabs[j]! (U j) :=
  ⟨unpack_eq_of_bindArrK (allN_spec bindU j hj), (u1 hj).1⟩

theorem a0 : cn (X 0) = true ∧ memU U (X 0) = true ∧ X 0 ≠ idn ∧ W 32 < S.cnt ∧
    S.T (W 32) = X 0 ∧ pc (X 0) (X 2) = pc (X 2) (X 0) := by
  have h := a0_ok
  unfold a0K at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  refine ⟨h.1, h.2.1, fun e => ?_, h.2.2.2.1, Nat.eq_of_beq_eq_true h.2.2.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2.2.2⟩
  have h3 := h.2.2.1
  rw [e, Nat.beq_refl] at h3
  exact absurd h3 (by decide)

theorem pR : P r₂T (X 2) := by
  have h := bindX
  simp only [Bool.and_eq_true] at h
  have hr := r_ok
  unfold rK at hr
  exact ⟨unpack_eq_of_bindArrK h.2, ((bAnd_iff _ _).1 hr).1⟩

theorem pA : P a0T (X 0) := by
  have h := bindX
  simp only [Bool.and_eq_true] at h
  exact ⟨unpack_eq_of_bindArrK h.1.1, a0.1⟩

theorem zz : cn (X 1) = true ∧ W 33 < S.cnt ∧ S.T (W 33) = X 1 ∧
    pc (X 1) (X 2) = pc (X 2) (X 1) ∧ at0 (X 1) = 0 ∧ pc (pc (X 1) (X 1)) (X 1) = idn ∧
    X 1 ≠ idn ∧ ∀ j < 16, pc (X 1) (U j) = pc (U j) (X 1) → U j = idn := by
  have h := z_ok
  unfold zK at h
  simp only [bAnd_iff, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h6, fun e => ?_, fun j hj hc => ?_⟩
  · rw [e, Nat.beq_refl] at h7
    exact absurd h7 (by decide)
  · have h := allN_spec h8 j hj
    have hb : Nat.beq (pc (X 1) (U j)) (pc (U j) (X 1)) = true := by
      rw [hc]
      exact Nat.beq_refl _
    rw [hb] at h
    exact Nat.eq_of_beq_eq_true h

theorem pZ : P zT (X 1) := by
  have h := bindX
  simp only [Bool.and_eq_true] at h
  exact ⟨unpack_eq_of_bindArrK h.1.2, zz.1⟩

@[expose] noncomputable def E : Enum := penumRec 42 6 S.cnt S.T S.PL

theorem cnt_eq : S.cnt = 20160 := Nat.eq_of_beq_eq_true cnt_ok

theorem chunks {L N : Nat} {Q : Nat → Prop} (hL : 0 < L)
    (h : ∀ s < N, ∀ i, Nat.mul s L ≤ i → i < Nat.mul s L + L → Q i) : ∀ i < N * L, Q i := by
  intro i hi
  exact h (i / L) (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)) i
    (Nat.div_mul_le_self i L) (Nat.lt_div_mul_add hL)

theorem sK_spec {G T PL POS SRT SRI U V : Nat → Nat} {R cnt lo len : Nat}
    (h : sK G T PL POS SRT SRI U V R cnt lo len = true) :
    ∀ i, lo ≤ i → i < lo + len → i < cnt →
      penumPtK 42 6 (mask 6) (42 * 6) false G G 3 cnt T PL POS SRT SRI i = true ∧
        puK T U i = true ∧ redK T U V R cnt i = true := by
  intro i h1 h2 h3
  have h' := allN_spec h (i - lo) (by omega)
  rw [strictB_app'] at h'
  have e : Nat.add lo (i - lo) = i := by
    change lo + (i - lo) = i
    omega
  rw [e] at h'
  have hb : Nat.blt i cnt = true := Eq.mpr Nat.blt_eq h3
  rw [hb] at h'
  obtain ⟨p1, p2⟩ := (bAnd_iff _ _).1 h'
  exact ⟨p1, (bAnd_iff _ _).1 p2⟩

theorem pts : ∀ i < S.cnt,
    penumPtK 42 6 (mask 6) (42 * 6) false S.G S.G 3 S.cnt S.T S.PL S.POS S.SRT S.SRI i = true ∧
      puK S.T U i = true ∧ redK S.T U V (X 2) S.cnt i = true := by
  intro i hi
  rw [cnt_eq] at hi
  refine chunks (N := 315) (L := 64) (Q := fun i =>
    penumPtK 42 6 (mask 6) (42 * 6) false S.G S.G 3 S.cnt S.T S.PL S.POS S.SRT S.SRI i = true ∧
      puK S.T U i = true ∧ redK S.T U V (X 2) S.cnt i = true) (by norm_num)
    (fun s hs j h1 h2 => ?_) i hi
  have h2' : j < s * 64 + 64 := h2
  exact sK_spec (S.all s hs) j h1 h2 (by rw [cnt_eq]; omega)

theorem hp : ∀ i < S.cnt,
    penumPtK 42 6 (mask 6) (42 * 6) false S.G S.G 3 S.cnt S.T S.PL S.POS S.SRT S.SRI i = true :=
  fun i hi => (pts i hi).1

theorem hE : enumBFS 42 gensS 20160 = E := (penumK_left_sound hn gensOK hd_ok hp).1

theorem tabs_size : E.tabs.size = S.cnt := by simp [E, penumRec]

theorem pT {k : Nat} (hk : k < S.cnt) : P E.tabs[k]! (S.T k) := by
  refine ⟨?_, penumPt_canon (hp k hk)⟩
  rw [getElem!_pos _ k (by rw [tabs_size]; exact hk)]
  simp [E, penumRec]

theorem foundS {x : Tab} {Q : Nat} (hx : P x Q) {q : Nat} (hq : q < S.cnt) (e : S.T q = Q) :
    found (indexOf E.tabs) E.tabs x = true := by
  rw [hx.1]
  exact (found_penumRec_iff hp hx.2).2 ⟨q, hq, e⟩

theorem foundU {x : Tab} {Q : Nat} (hx : P x Q) (h : memU U Q = true) :
    found (indexOf uTabs) uTabs x = true := by
  obtain ⟨l, hl, e⟩ := memU_spec h
  rw [found_indexOf_iff]
  refine ⟨l, by rw [uSize]; exact hl, ?_⟩
  rw [(pU hl).1, hx.1, e]

theorem memE {x : Tab} (hx : x ∈ E.tabs.toList) : ∃ k < S.cnt, P x (S.T k) := by
  obtain ⟨k, hk, e⟩ := List.getElem_of_mem hx
  have hk' : k < E.tabs.size := by simpa using hk
  refine ⟨k, by rw [← tabs_size]; exact hk', ?_⟩
  have h := pT (k := k) (by rw [← tabs_size]; exact hk')
  rw [getElem!_pos _ k hk'] at h
  simp only [Array.getElem_toList] at e
  rwa [← e]

theorem memE_of {k : Nat} (hk : k < S.cnt) : E.tabs[k]! ∈ E.tabs.toList := by
  rw [getElem!_pos _ k (by rw [tabs_size]; exact hk)]
  exact Array.getElem_mem_toList _

theorem memC {x : Tab} : x ∈ (centTabs 42 E.tabs r₂T).toList ↔
    x ∈ E.tabs.toList ∧ (comp 42 x r₂T == comp 42 r₂T x) = true := by
  unfold centTabs
  rw [Array.toList_filter, List.mem_filter]

theorem commP {x : Tab} {Q : Nat} (hx : P x Q) :
    (comp 42 x r₂T == comp 42 r₂T x) = Nat.beq (pc Q (X 2)) (pc (X 2) Q) :=
  beqP (compP hx pR) (compP pR hx)

theorem foundC {x : Tab} {Q : Nat} (hx : P x Q) {q : Nat} (hq : q < S.cnt) (e : S.T q = Q)
    (hc : pc Q (X 2) = pc (X 2) Q) :
    found (indexOf (centTabs 42 E.tabs r₂T)) (centTabs 42 E.tabs r₂T) x = true := by
  rw [found_indexOf_iff]
  have hm : x ∈ (centTabs 42 E.tabs r₂T).toList := by
    rw [memC, commP hx, hc, Nat.beq_refl]
    refine ⟨?_, rfl⟩
    have h := memE_of hq
    have hq' := pT hq
    rwa [hq'.1, e, ← hx.1] at h
  obtain ⟨i, hi, e'⟩ := List.getElem_of_mem hm
  refine ⟨i, by simpa using hi, ?_⟩
  rw [getElem!_pos _ i (by simpa using hi)]
  simpa using e'

theorem conjP {g x : Tab} {G Q : Nat} (hg : P g G) (hx : P x Q)
    (h : invOK G (pinv G) = true) :
    P (conjTab 42 g (invTab 42 g) x) (pc (pc G Q) (pinv G)) :=
  compP (compP hg hx) (invP hg h).1

theorem scanU1_true : scanU1 = true := by
  unfold scanU1
  dsimp only
  rw [hE]
  refine allBelow_of fun i hi => ?_
  rw [uSize] at hi
  obtain ⟨-, hw, he, h0, hsq⟩ := u1 hi
  have hP := pU hi
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨foundS hP hw he, by rw [getP hP, h0]⟩, ?_⟩
  rw [← beq_iff_eq, beqP (compP hP hP) idP, hsq]
  exact Nat.beq_refl _

theorem scanU2_true : scanU2 = true := by
  unfold scanU2
  dsimp only
  refine allBelow_of fun i hi => allBelow_of fun j hj => ?_
  rw [uSize] at hi hj
  exact foundU (compP (pU hi) (pU hj)) (allN_spec (allN_spec u2_ok i hi) j hj)

theorem scanU3_true : scanU3 = true := foundU idP u3_ok

theorem scanR_true : scanR = true := by
  unfold scanR
  dsimp only
  have hr := r_ok
  unfold rK at hr
  simp only [bAnd_iff] at hr
  obtain ⟨-, h2, h3⟩ := hr
  rw [Bool.and_eq_true, beqP (compP pR pR) idP]
  refine ⟨h2, allBelow_of fun j hj => ?_⟩
  rw [uSize] at hj
  exact foundU (compP (compP pR (pU hj)) pR) (allN_spec h3 j hj)

theorem scanA0_true : scanA0 = true := by
  unfold scanA0
  dsimp only
  rw [hE]
  obtain ⟨-, hm, hne, hq, he, hc⟩ := a0
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨foundU pA hm, ?_⟩, foundC pA hq he hc⟩
  rw [beqP pA idP]
  cases hb : Nat.beq (X 0) idn
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) hne

theorem trans_facts {j : Nat} (hj : j < 16) (hne : U j ≠ idn) : WT j < S.cnt ∧
    at0 (S.T (WT j)) = 0 ∧ invOK (S.T (WT j)) (pinv (S.T (WT j))) = true ∧
    pc (pc (S.T (WT j)) (X 0)) (pinv (S.T (WT j))) = U j := by
  have h := allN_spec trans_ok j hj
  have hb : Nat.beq (U j) idn = false := by
    cases hb : Nat.beq (U j) idn
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  rw [hb] at h
  change strictB (WT j) _ = true at h
  rw [strictB_app'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [strictB_app'] at h2
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  rw [strictB_app'] at h3
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h3
  exact ⟨Eq.mp Nat.blt_eq h1, Nat.eq_of_beq_eq_true h2, h3, Nat.eq_of_beq_eq_true h4⟩

theorem scanTrans_true : scanTrans = true := by
  unfold scanTrans
  dsimp only
  rw [hE]
  refine allBelow_of fun j hj => ?_
  rw [uSize] at hj
  have hP := pU hj
  rw [Bool.or_eq_true]
  by_cases hid : U j = idn
  · left
    rw [beqP hP idP, hid, Nat.beq_refl]
  · right
    obtain ⟨hk, h0, hinv, hc⟩ := trans_facts hj hid
    refine anyBelow_of (i := WT j) (by rw [tabs_size]; exact hk) ?_
    have hX := pT hk
    obtain ⟨-, hs, hi⟩ := invP hX hinv
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, hs⟩, hi⟩, ?_⟩
    · rw [getP hX, h0]
      rfl
    · rw [beqP (conjP hX pA hinv) hP, hc, Nat.beq_refl]

theorem scanZ_true : scanZ = true := by
  unfold scanZ
  dsimp only
  rw [hE]
  obtain ⟨-, hq, he, hc, h0, h3, hne, hu⟩ := zz
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨foundC pZ hq he hc, ?_⟩, ?_⟩, ?_⟩, allBelow_of fun j hj => ?_⟩
  · rw [getP pZ, h0]
    rfl
  · rw [beqP (compP (compP pZ pZ) pZ) idP, h3, Nat.beq_refl]
  · rw [beqP pZ idP]
    cases hb : Nat.beq (X 1) idn
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hne
  · rw [uSize] at hj
    have hP := pU hj
    rw [Bool.or_eq_true, beqP (compP pZ hP) (compP hP pZ), beqP hP idP]
    by_cases hcz : pc (X 1) (U j) = pc (U j) (X 1)
    · right
      rw [hu j hj hcz, Nat.beq_refl]
    · left
      cases hb : Nat.beq (pc (X 1) (U j)) (pc (U j) (X 1))
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hcz

theorem scanWit_true : scanWit = true := by
  unfold scanWit
  refine allBelow_of fun j hj => ?_
  rw [uSize] at hj
  have hP := pU hj
  have h := allN_spec wit_ok j hj
  rw [Bool.or_eq_true, beqP (compP pR hP) (compP hP pR)]
  cases hb : Nat.beq (pc (X 2) (U j)) (pc (U j) (X 2))
  · left
    rfl
  · right
    rw [hb] at h
    obtain ⟨i, hi, e⟩ := anyK_spec h
    refine anyBelow_of (i := i) (by rw [uSize]; exact hi) ?_
    rw [beqP (compP (compP (compP pR (pU hi)) pR) (pU hi)) hP]
    exact e

theorem pu_facts {k : Nat} (hk : k < S.cnt) (h0 : at0 (S.T k) = 0) :
    invOK (S.T k) (pinv (S.T k)) = true ∧
      ∀ j < 16, memU U (pc (pc (S.T k) (U j)) (pinv (S.T k))) = true := by
  have h := (pts k hk).2.1
  unfold puK at h
  rw [strictB_app', h0, Nat.beq_refl] at h
  change strictB (pinv (S.T k)) _ = true at h
  rw [strictB_app'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨h1, allN_spec h2⟩

theorem scanPU_true : scanPU = true := by
  unfold scanPU
  dsimp only
  rw [hE]
  refine allBelow_of fun k hk => ?_
  rw [tabs_size] at hk
  have hX := pT hk
  rw [Bool.or_eq_true, getP hX]
  by_cases h0 : at0 (S.T k) = 0
  · right
    obtain ⟨hinv, hu⟩ := pu_facts hk h0
    obtain ⟨-, hs, hi⟩ := invP hX hinv
    simp only [Bool.and_eq_true]
    refine ⟨⟨hs, hi⟩, allBelow_of fun j hj => ?_⟩
    rw [uSize] at hj
    exact foundU (conjP hX (pU hj) hinv) (hu j hj)
  · left
    simpa using h0

theorem red_facts {k : Nat} (hk : k < S.cnt) (hc : pc (S.T k) (X 2) = pc (X 2) (S.T k))
    (hs : pc (S.T k) (S.T k) = idn) : V k < S.cnt ∧
      pc (S.T (V k)) (X 2) = pc (X 2) (S.T (V k)) ∧
      invOK (S.T (V k)) (pinv (S.T (V k))) = true ∧
      memU U (pc (pc (S.T (V k)) (S.T k)) (pinv (S.T (V k)))) = true := by
  have h := (pts k hk).2.2
  unfold redK at h
  rw [strictB_app', hc, hs, Nat.beq_refl, Nat.beq_refl] at h
  change strictB (V k) _ = true at h
  rw [strictB_app'] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  rw [strictB_app'] at h2
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  rw [strictB_app'] at h3
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h3
  exact ⟨Eq.mp Nat.blt_eq h1, Nat.eq_of_beq_eq_true h2, h3, h4⟩

theorem scanRed_true : scanRed = true := by
  unfold scanRed
  dsimp only
  rw [hE]
  refine allBelow_mem (f := fun x => !(comp 42 x x == idTab 42) ||
    anyBelow (centTabs 42 E.tabs r₂T).size fun j =>
      (invTab 42 (centTabs 42 E.tabs r₂T)[j]!).size == 42 &&
        comp 42 (invTab 42 (centTabs 42 E.tabs r₂T)[j]!) (centTabs 42 E.tabs r₂T)[j]! ==
          idTab 42 &&
        found (indexOf uTabs) uTabs (conjTab 42 (centTabs 42 E.tabs r₂T)[j]!
          (invTab 42 (centTabs 42 E.tabs r₂T)[j]!) x)) fun x hx => ?_
  obtain ⟨hxE, hxc⟩ := memC.1 hx
  obtain ⟨k, hk, hX⟩ := memE hxE
  rw [commP hX] at hxc
  have hc := Nat.eq_of_beq_eq_true hxc
  simp only [Bool.or_eq_true, Bool.not_eq_true', beqP (compP hX hX) idP]
  by_cases hs : pc (S.T k) (S.T k) = idn
  · right
    obtain ⟨hy, hyc, hinv, hm⟩ := red_facts hk hc hs
    have hY := pT hy
    have hyC : E.tabs[V k]! ∈ (centTabs 42 E.tabs r₂T).toList := by
      rw [memC, commP hY, hyc, Nat.beq_refl]
      exact ⟨memE_of hy, rfl⟩
    refine anyBelow_mem (f := fun y => (invTab 42 y).size == 42 &&
      comp 42 (invTab 42 y) y == idTab 42 &&
      found (indexOf uTabs) uTabs (conjTab 42 y (invTab 42 y) x)) hyC ?_
    obtain ⟨-, h1, h2⟩ := invP hY hinv
    simp only [Bool.and_eq_true]
    exact ⟨⟨h1, h2⟩, foundU (conjP hY hX hinv) hm⟩
  · left
    cases hb : Nat.beq (pc (S.T k) (S.T k)) idn
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) hs

end CFSG.KD.LQT.TA

end
