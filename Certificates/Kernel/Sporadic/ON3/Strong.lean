
module

public import Certificates.Kernel.Sporadic.ON3.Elements

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON3

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KS.TW CFSG.KS.PW CFSG.KS.Words
open CertificateChecks.KernelSpor.ON (TT UU TT_lt UU_lt TT_UU perm_facts')

@[expose] def InvPair (n m : Nat) (G GI : Nat → Nat → Nat) : Prop :=
  ∀ i < m, ∀ y < n, G i y < n ∧ GI i y < n ∧ GI i (G i y) = y ∧ G i (GI i y) = y

@[expose] def LetM (m : Nat) (w : List Int) : Prop := ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ m

theorem invW_invW (w : List Int) : invW (invW w) = w := by
  simp [invW, List.map_reverse]

theorem letM_invW {m : Nat} {w : List Int} (h : LetM m w) : LetM m (invW w) := by
  intro l hl
  simp only [invW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨z, hz, rfl⟩ := hl
  obtain ⟨h1, h2⟩ := h z hz
  exact ⟨by omega, by omega⟩

theorem gz_inv {n m : Nat} {G GI : Nat → Nat → Nat} (h : InvPair n m G GI) {z : Int}
    (hz : z ≠ 0 ∧ z.natAbs ≤ m) {y : Nat} (hy : y < n) :
    GZ G GI z y < n ∧ GZ G GI (-z) (GZ G GI z y) = y := by
  unfold GZ
  by_cases hp : 0 < z
  · have hi : z.toNat - 1 < m := by omega
    have hn : ¬ 0 < -z := by omega
    have e : (-(-z)).toNat - 1 = z.toNat - 1 := by omega
    simp only [hp, hn, ite_true, ite_false, e]
    exact ⟨(h _ hi y hy).1, (h _ hi y hy).2.2.1⟩
  · have hi : (-z).toNat - 1 < m := by omega
    have hn : 0 < -z := by omega
    simp only [hp, hn, ite_true, ite_false]
    exact ⟨(h _ hi y hy).2.1, (h _ hi y hy).2.2.2⟩

theorem invPair_word {n m : Nat} {G GI : Nat → Nat → Nat} (h : InvPair n m G GI) {w : List Int}
    (hw : LetM m w) : ∀ y < n, w.foldr (GZ G GI) y < n ∧ (invW w).foldr (GZ G GI) y < n ∧
      (invW w).foldr (GZ G GI) (w.foldr (GZ G GI) y) = y ∧
      w.foldr (GZ G GI) ((invW w).foldr (GZ G GI) y) = y := by
  intro y hy
  have h1 := foldr_inv (n := n) (G := GZ G GI) w (fun z hz y hy => gz_inv h (hw z hz) hy) y hy
  have h2 := foldr_inv (n := n) (G := GZ G GI) (invW w)
    (fun z hz y hy => gz_inv h (letM_invW hw z hz) hy) y hy
  have e : ((invW w).reverse.map fun z => -z) = w := invW_invW w
  rw [e] at h2
  exact ⟨h1.1, h2.1, h1.2, h2.2⟩

theorem foldr_congr {G GI G' GI' : Nat → Nat → Nat} {m : Nat}
    (hG : ∀ i < m, G i = G' i) (hGI : ∀ i < m, GI i = GI' i) :
    ∀ w : List Int, LetM m w → ∀ x, w.foldr (GZ G GI) x = w.foldr (GZ G' GI') x
  | [], _, _ => rfl
  | l :: w, hw, x => by
    simp only [List.foldr_cons]
    rw [foldr_congr hG hGI w (fun z hz => hw z (List.mem_cons_of_mem l hz)) x]
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    unfold GZ
    by_cases hp : 0 < l
    · simp only [hp, ite_true]
      rw [hG _ (by omega)]
    · simp only [hp, ite_false]
      rw [hGI _ (by omega)]

theorem tt_pair : InvPair 245520 7 TT UU := fun i hi y hy =>
  ⟨TT_lt hy, UU_lt hy, (perm_facts' y hy i hi).2.2, TT_UU hi hy⟩

theorem tr_word (G GI : Nat → Nat → Nat) {k : Nat} (hk : k < 23) (x : Nat) :
    CFSG.KS.ON.trace G GI (ON3W.WC k) (ON3W.WL k) x = (wordL.getD k []).foldr (GZ G GI) x := by
  rw [trace_eq, dec_eq hk]

theorem tr_inv (G GI : Nat → Nat → Nat) {k : Nat} (hk : k < 23) (x : Nat) :
    CFSG.KS.ON.trace G GI (ON3W.WC (k + 23)) (ON3W.WL (k + 23)) x =
      (invW (wordL.getD k [])).foldr (GZ G GI) x := by
  rw [trace_eq, dec_inv hk]

theorem strong_letters : ((wordL.getD 17 []).all fun l => l != 0 && decide (l.natAbs ≤ 6)) &&
    ((wordL.getD 18 []).all fun l => l != 0 && decide (l.natAbs ≤ 7)) &&
    ((wordL.getD 19 []).all fun l => l != 0 && decide (l.natAbs ≤ 3)) &&
    ((wordL.getD 20 []).all fun l => l != 0 && decide (l.natAbs ≤ 4)) &&
    ((wordL.getD 21 []).all fun l => l != 0 && decide (l.natAbs ≤ 2)) &&
    ((wordL.getD 22 []).all fun l => l != 0 && decide (l.natAbs ≤ 3)) = true := by
  decide +kernel

theorem letM_of {m : Nat} {w : List Int}
    (h : (w.all fun l => l != 0 && decide (l.natAbs ≤ m)) = true) : LetM m w := by
  intro l hl
  have h' := List.all_eq_true.1 h l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h'
  exact h'

theorem strong_lets : LetM 6 (wordL.getD 17 []) ∧ LetM 7 (wordL.getD 18 []) ∧
    LetM 3 (wordL.getD 19 []) ∧ LetM 4 (wordL.getD 20 []) ∧ LetM 2 (wordL.getD 21 []) ∧
    LetM 3 (wordL.getD 22 []) := by
  have h := strong_letters
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨letM_of h1, letM_of h2, letM_of h3, letM_of h4, letM_of h5, letM_of h6⟩

theorem word_pair {k : Nat} (hk : k < 17) : ∀ y < 245520, trW k y < 245520 ∧
    trW (k + 23) y < 245520 ∧ trW (k + 23) (trW k y) = y ∧ trW k (trW (k + 23) y) = y := by
  intro y hy
  unfold trW
  simp only [tr_word TT UU (k := k) (by omega), tr_inv TT UU (k := k) (by omega)]
  exact invPair_word tt_pair (let7 hk) y hy

theorem tG_pair : InvPair 245520 6 tG tGI := by
  intro i hi y hy
  have a1 : Nat.add (nat_lit 11) i = i + 11 := Nat.add_comm 11 i
  have a2 : Nat.add (nat_lit 34) i = i + 11 + 23 := by
    rw [Nat.add_assoc]
    exact Nat.add_comm 34 i
  have e1 : tG i = trW (i + 11) := by
    funext x
    unfold tG
    rw [a1]
  have e2 : tGI i = trW (i + 11 + 23) := by
    funext x
    unfold tGI
    rw [a2]
  rw [e1, e2]
  exact word_pair (by omega) y hy

theorem tG7_lo {i : Nat} (hi : i < 6) : tG7 i = tG i := by
  funext x
  unfold tG7
  rw [blt_of hi]

theorem tGI7_lo {i : Nat} (hi : i < 6) : tGI7 i = tGI i := by
  funext x
  unfold tGI7
  rw [blt_of hi]

theorem tS6_eq (x : Nat) : tS6 x = (wordL.getD 17 []).foldr (GZ tG tGI) x := by
  unfold tS6
  exact tr_word _ _ (by norm_num) x

theorem tS6I_eq (x : Nat) : tS6I x = (invW (wordL.getD 17 [])).foldr (GZ tG tGI) x := by
  unfold tS6I
  exact tr_inv _ _ (k := 17) (by norm_num) x

theorem tG7_pair : InvPair 245520 7 tG7 tGI7 := by
  intro i hi y hy
  rcases Nat.lt_or_ge i 6 with h | h
  · rw [tG7_lo h, tGI7_lo h]
    exact tG_pair i h y hy
  · have e : i = 6 := by omega
    subst e
    have a1 : tG7 6 = tS6 := rfl
    have a2 : tGI7 6 = tS6I := rfl
    rw [a1, a2]
    simp only [tS6_eq, tS6I_eq]
    exact invPair_word tG_pair strong_lets.1 y hy

theorem tF_lo {i : Nat} (hi : i < 7) : tF i = tG7 i := by
  funext x
  unfold tF
  rw [blt_of hi]

theorem tFI_lo {i : Nat} (hi : i < 7) : tFI i = tGI7 i := by
  funext x
  unfold tFI
  rw [blt_of hi]

theorem tS7_eq (x : Nat) : tS7 x = (wordL.getD 18 []).foldr (GZ tG7 tGI7) x := by
  unfold tS7
  exact tr_word _ _ (by norm_num) x

theorem tS7I_eq (x : Nat) : tS7I x = (invW (wordL.getD 18 [])).foldr (GZ tG7 tGI7) x := by
  unfold tS7I
  exact tr_inv _ _ (k := 18) (by norm_num) x

theorem tF_pair : InvPair 245520 8 tF tFI := by
  intro i hi y hy
  rcases Nat.lt_or_ge i 7 with h | h
  · rw [tF_lo h, tFI_lo h]
    exact tG7_pair i h y hy
  · have e : i = 7 := by omega
    subst e
    have a1 : tF 7 = tS7 := rfl
    have a2 : tFI 7 = tS7I := rfl
    rw [a1, a2]
    simp only [tS7_eq, tS7I_eq]
    exact invPair_word tG7_pair strong_lets.2.1 y hy

theorem tG_eq {h : Nat} (hh : h < 6) (x : Nat) :
    tG h x = (wordL.getD (Nat.add 11 h) []).foldr (GZ TT UU) x := by
  unfold tG trW
  exact tr_word _ _ (by simp only [Nat.add_eq]; omega) x

theorem twords_size : (wordArrs Data.TWords).size = 6 := by
  rw [wordArrs, pwords_eq, Array.size_map]
  rfl

theorem tStrong_get : TStrong.size = 8 ∧
    ∀ j < 8, TStrong[j]! = Array.ofFn (n := 245520) fun i => tF j i.val := by
  unfold TStrong
  refine extendStrong_get (m := 6) twords_size rfl (by norm_num) ?_ ?_
    (fun j hj x hx => ⟨(tF_pair j hj x hx).1, (tF_pair j hj x hx).2.1, (tF_pair j hj x hx).2.2.1⟩)
  · intro j hj
    rw [wordArrs_get (Nat.lt_of_lt_of_eq hj rfl)]
    have hw : Let7 Data.TWords[j]! := by
      interval_cases j
      · exact let7 (k := 11) (by norm_num)
      · exact let7 (k := 12) (by norm_num)
      · exact let7 (k := 13) (by norm_num)
      · exact let7 (k := 14) (by norm_num)
      · exact let7 (k := 15) (by norm_num)
      · exact let7 (k := 16) (by norm_num)
    rw [wordArr_eq hw]
    congr 1
    funext i
    rw [tF_lo (by omega), tG7_lo hj, tG_eq hj]
    interval_cases j <;> rfl
  · intro j h6 h8
    interval_cases j
    · refine ⟨strong_lets.1, fun x _ => ?_⟩
      have a1 : tF 6 x = tS6 x := rfl
      rw [a1, tS6_eq]
      exact foldr_congr (m := 6) (fun i hi => by rw [tF_lo (by omega), tG7_lo hi])
        (fun i hi => by rw [tFI_lo (by omega), tGI7_lo hi]) _ strong_lets.1 x
    · refine ⟨strong_lets.2.1, fun x _ => ?_⟩
      have a1 : tF 7 x = tS7 x := rfl
      rw [a1, tS7_eq]
      exact foldr_congr (m := 7) (fun i hi => by rw [tF_lo hi]) (fun i hi => by rw [tFI_lo hi]) _
        strong_lets.2.1 x

theorem nIf_lo {c : Bool} (hc : c = true) (t e : Nat) : nIf(c, t, e) = t := by
  subst hc
  rfl

theorem tab_pair {k : Nat} (hk : k < 17) {T : Nat → Nat} (hT : ∀ y < 245520, T y = trW k y)
    {y : Nat} (hy : y < 245520) : T y < 245520 ∧ trW (k + 23) y < 245520 ∧
      trW (k + 23) (T y) = y ∧ T (trW (k + 23) y) = y := by
  obtain ⟨w1, w2, w3, w4⟩ := word_pair hk y hy
  rw [hT y hy, hT _ w2]
  exact ⟨w1, w2, w3, w4⟩

theorem mG_pair : InvPair 245520 3 mG mGI := by
  intro i hi y hy
  interval_cases i
  · have e1 : mG 0 y = ZT y := rfl
    have e2 : mGI 0 y = ZT y := rfl
    have e3 : mG 0 (mGI 0 y) = ZT (ZT y) := rfl
    have e4 : mGI 0 (mG 0 y) = ZT (ZT y) := rfl
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hz, -⟩ := tab_facts hy
    rw [e1, e2]
    exact ⟨(z_get y hy).2, (z_get y hy).2, hz, hz⟩
  · exact tab_pair (k := 7) (T := M2T) (by norm_num)
      (fun x hx => (tab_facts hx).2.2.2.2.2.2.2.2.1) hy
  · exact tab_pair (k := 8) (T := M3T) (by norm_num)
      (fun x hx => (tab_facts hx).2.2.2.2.2.2.2.2.2.1) hy

theorem mG4_lo {i : Nat} (hi : i < 3) : mG4 i = mG i := by
  funext x
  unfold mG4
  rw [blt_of hi]

theorem mGI4_lo {i : Nat} (hi : i < 3) : mGI4 i = mGI i := by
  funext x
  unfold mGI4
  rw [blt_of hi]

theorem mF_lo {i : Nat} (hi : i < 4) : mF i = mG4 i := by
  funext x
  unfold mF
  rw [blt_of hi]

theorem mFI_lo {i : Nat} (hi : i < 4) : mFI i = mGI4 i := by
  funext x
  unfold mFI
  rw [blt_of hi]

theorem mS3_eq (x : Nat) : mS3 x = (wordL.getD 19 []).foldr (GZ mG mGI) x := by
  unfold mS3
  exact tr_word _ _ (by norm_num) x

theorem mS3I_eq (x : Nat) : mS3I x = (invW (wordL.getD 19 [])).foldr (GZ mG mGI) x := by
  unfold mS3I
  exact tr_inv _ _ (k := 19) (by norm_num) x

theorem mS4_eq (x : Nat) : mS4 x = (wordL.getD 20 []).foldr (GZ mG4 mGI4) x := by
  unfold mS4
  exact tr_word _ _ (by norm_num) x

theorem mS4I_eq (x : Nat) : mS4I x = (invW (wordL.getD 20 [])).foldr (GZ mG4 mGI4) x := by
  unfold mS4I
  exact tr_inv _ _ (k := 20) (by norm_num) x

theorem mG4_pair : InvPair 245520 4 mG4 mGI4 := by
  intro i hi y hy
  rcases Nat.lt_or_ge i 3 with h | h
  · rw [mG4_lo h, mGI4_lo h]
    exact mG_pair i h y hy
  · have e : i = 3 := by omega
    subst e
    have a1 : mG4 3 = mS3 := rfl
    have a2 : mGI4 3 = mS3I := rfl
    rw [a1, a2]
    simp only [mS3_eq, mS3I_eq]
    exact invPair_word mG_pair strong_lets.2.2.1 y hy

theorem mF_pair : InvPair 245520 5 mF mFI := by
  intro i hi y hy
  rcases Nat.lt_or_ge i 4 with h | h
  · rw [mF_lo h, mFI_lo h]
    exact mG4_pair i h y hy
  · have e : i = 4 := by omega
    subst e
    have a1 : mF 4 = mS4 := rfl
    have a2 : mFI 4 = mS4I := rfl
    rw [a1, a2]
    simp only [mS4_eq, mS4I_eq]
    exact invPair_word mG4_pair strong_lets.2.2.2.1 y hy

theorem orig_eq {g : Array Nat} {F : Nat → Nat} (hs : g.size = 245520)
    (h : ∀ x < 245520, g[x]! = F x) : g = Array.ofFn (n := 245520) fun i => F i.val :=
  arr_ext hs h

theorem wordArrs_size_get {ws : Array (List Int)} {j : Nat} (hj : j < ws.size) :
    (wordArrs ws)[j]!.size = 245520 := by
  rw [wordArrs_get hj]
  exact pword_size _

theorem mStrong_get : MStrong.size = 5 ∧
    ∀ j < 5, MStrong[j]! = Array.ofFn (n := 245520) fun i => mF j i.val := by
  unfold MStrong
  refine extendStrong_get (m := 3) (by rw [wordArrs, pwords_eq, Array.size_map]; rfl) rfl
    (by norm_num) ?_ ?_
    (fun j hj x hx => ⟨(mF_pair j hj x hx).1, (mF_pair j hj x hx).2.1, (mF_pair j hj x hx).2.2.1⟩)
  · intro j hj
    refine orig_eq (wordArrs_size_get (Nat.lt_of_lt_of_eq hj rfl))
      fun x hx => ?_
    rw [mF_lo (by omega), mG4_lo hj]
    exact (m_get hj x hx).1
  · intro j h3 h5
    interval_cases j
    · refine ⟨strong_lets.2.2.1, fun x _ => ?_⟩
      have a1 : mF 3 x = mS3 x := rfl
      rw [a1, mS3_eq]
      exact foldr_congr (m := 3) (fun i hi => by rw [mF_lo (by omega), mG4_lo hi])
        (fun i hi => by rw [mFI_lo (by omega), mGI4_lo hi]) _ strong_lets.2.2.1 x
    · refine ⟨strong_lets.2.2.2.1, fun x _ => ?_⟩
      have a1 : mF 4 x = mS4 x := rfl
      rw [a1, mS4_eq]
      exact foldr_congr (m := 4) (fun i hi => by rw [mF_lo hi]) (fun i hi => by rw [mFI_lo hi]) _
        strong_lets.2.2.2.1 x

theorem lG_pair : InvPair 245520 2 lG lGI := by
  intro i hi y hy
  interval_cases i
  · exact tab_pair (k := 9) (T := L1T) (by norm_num)
      (fun x hx => (tab_facts hx).2.2.2.2.2.2.2.2.2.2.1) hy
  · exact tab_pair (k := 10) (T := L2T) (by norm_num)
      (fun x hx => (tab_facts hx).2.2.2.2.2.2.2.2.2.2.2.1) hy

theorem lG3_lo {i : Nat} (hi : i < 2) : lG3 i = lG i := by
  funext x
  unfold lG3
  rw [blt_of hi]

theorem lGI3_lo {i : Nat} (hi : i < 2) : lGI3 i = lGI i := by
  funext x
  unfold lGI3
  rw [blt_of hi]

theorem lF_lo {i : Nat} (hi : i < 3) : lF i = lG3 i := by
  funext x
  unfold lF
  rw [blt_of hi]

theorem lFI_lo {i : Nat} (hi : i < 3) : lFI i = lGI3 i := by
  funext x
  unfold lFI
  rw [blt_of hi]

theorem lS2_eq (x : Nat) : lS2 x = (wordL.getD 21 []).foldr (GZ lG lGI) x := by
  unfold lS2
  exact tr_word _ _ (by norm_num) x

theorem lS2I_eq (x : Nat) : lS2I x = (invW (wordL.getD 21 [])).foldr (GZ lG lGI) x := by
  unfold lS2I
  exact tr_inv _ _ (k := 21) (by norm_num) x

theorem lS3_eq (x : Nat) : lS3 x = (wordL.getD 22 []).foldr (GZ lG3 lGI3) x := by
  unfold lS3
  exact tr_word _ _ (by norm_num) x

theorem lS3I_eq (x : Nat) : lS3I x = (invW (wordL.getD 22 [])).foldr (GZ lG3 lGI3) x := by
  unfold lS3I
  exact tr_inv _ _ (k := 22) (by norm_num) x

theorem lG3_pair : InvPair 245520 3 lG3 lGI3 := by
  intro i hi y hy
  rcases Nat.lt_or_ge i 2 with h | h
  · rw [lG3_lo h, lGI3_lo h]
    exact lG_pair i h y hy
  · have e : i = 2 := by omega
    subst e
    have a1 : lG3 2 = lS2 := rfl
    have a2 : lGI3 2 = lS2I := rfl
    rw [a1, a2]
    simp only [lS2_eq, lS2I_eq]
    exact invPair_word lG_pair strong_lets.2.2.2.2.1 y hy

theorem lF_pair : InvPair 245520 4 lF lFI := by
  intro i hi y hy
  rcases Nat.lt_or_ge i 3 with h | h
  · rw [lF_lo h, lFI_lo h]
    exact lG3_pair i h y hy
  · have e : i = 3 := by omega
    subst e
    have a1 : lF 3 = lS3 := rfl
    have a2 : lFI 3 = lS3I := rfl
    rw [a1, a2]
    simp only [lS3_eq, lS3I_eq]
    exact invPair_word lG3_pair strong_lets.2.2.2.2.2 y hy

theorem lStrong_get : LStrong.size = 4 ∧
    ∀ j < 4, LStrong[j]! = Array.ofFn (n := 245520) fun i => lF j i.val := by
  unfold LStrong
  refine extendStrong_get (m := 2) (by rw [wordArrs, pwords_eq, Array.size_map]; rfl) rfl
    (by norm_num) ?_ ?_
    (fun j hj x hx => ⟨(lF_pair j hj x hx).1, (lF_pair j hj x hx).2.1, (lF_pair j hj x hx).2.2.1⟩)
  · intro j hj
    refine orig_eq (wordArrs_size_get (Nat.lt_of_lt_of_eq hj rfl))
      fun x hx => ?_
    rw [lF_lo (by omega), lG3_lo hj]
    exact (l_get hj x hx).1
  · intro j h2 h4
    interval_cases j
    · refine ⟨strong_lets.2.2.2.2.1, fun x _ => ?_⟩
      have a1 : lF 2 x = lS2 x := rfl
      rw [a1, lS2_eq]
      exact foldr_congr (m := 2) (fun i hi => by rw [lF_lo (by omega), lG3_lo hi])
        (fun i hi => by rw [lFI_lo (by omega), lGI3_lo hi]) _ strong_lets.2.2.2.2.1 x
    · refine ⟨strong_lets.2.2.2.2.2, fun x _ => ?_⟩
      have a1 : lF 3 x = lS3 x := rfl
      rw [a1, lS3_eq]
      exact foldr_congr (m := 3) (fun i hi => by rw [lF_lo hi]) (fun i hi => by rw [lFI_lo hi]) _
        strong_lets.2.2.2.2.2 x

end CertificateChecks.KernelSpor.ON3

end
