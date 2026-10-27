module

public import Certificates.Kernel.FzUT.BModTab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzBK1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzAssump

public section

namespace CFSG.KC.FzBMod

open Certificates.FzBU CFSG.OddStandard.SmallF3.FritzII

theorem allN_iff (n : Nat) (f : Nat → Bool) : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change (Bool.rec (motive := fun _ => Bool) false (allN n f) (f n)) = true ↔ _
    cases hfn : f n with
    | false =>
      refine ⟨fun h => absurd h (by simp), fun h => absurd (h n (Nat.lt_succ_self n)) (by simp [hfn])⟩
    | true =>
      change allN n f = true ↔ _
      rw [ih]
      constructor
      · intro h i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | rfl
        · exact h i h'
        · exact hfn
      · exact fun h i hi => h i (Nat.lt_succ_of_lt hi)

theorem countN_eq (n : Nat) (f : Nat → Bool) :
    countN n f = ((Finset.range n).filter (fun i => f i = true)).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.add (Bool.rec (motive := fun _ => Nat) 0 1 (f n)) (countN n f) = _
    rw [ih, Finset.range_add_one, Finset.filter_insert]
    cases hfn : f n with
    | true =>
      rw [if_pos rfl, Finset.card_insert_of_notMem (by simp)]
      change 1 + _ = _
      omega
    | false =>
      rw [if_neg (by simp)]
      change 0 + _ = _
      omega

theorem wordTab_eq : wordTab () = ch441796WL.toArray := by
  have h : (wordTab ()).toList = ch441796WL := beq_iff_eq.mp ch441796_words
  rw [← h, Array.toArray_toList]

private theorem getElem!_map' {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {i : Nat} (h : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using h), Array.getElem_map, getElem!_pos a i h]

private theorem extArr_getElem! (W : Array (List Nat)) (y : Array Nat) {x : Nat} (hx : x < 64) :
    (extArr W y)[x]! = evalW y W[x]! := by
  unfold extArr
  rw [getElem!_pos _ x (by simpa using hx), Array.getElem_map, Array.getElem_range]

private theorem repImgs_size (c : Bool) : (repImgs c).size = 3 := by cases c <;> rfl

theorem lk6_lt (T x : Nat) : lk6 T x < 64 :=
  Nat.lt_of_le_of_lt (Nat.and_le_right) (by norm_num)

private theorem tab_of {c : Bool} {i : Nat} (hi : i < 3) {T : Nat}
    (h : ch441796TabB ((repImgs c)[i]!) T = true) {x : Nat} (hx : x < 64) :
    (((repImgs c).map (extArr (wordTab ())))[i]!)[x]! = lk6 T x := by
  rw [getElem!_map' _ _ (by rw [repImgs_size]; exact hi), extArr_getElem! _ _ hx, wordTab_eq]
  exact Nat.eq_of_beq_eq_true ((allN_iff 64 _).mp h x hx)

theorem aq_eq (c : Bool) {x : Nat} (hx : x < 64) : (modl c ()).aq[x]! = lk6 (tqT c) x :=
  tab_of (by norm_num) (ch441796_tab_q c) hx

theorem as_eq (c : Bool) {x : Nat} (hx : x < 64) : (modl c ()).as[x]! = lk6 (tsT c) x :=
  tab_of (by norm_num) (ch441796_tab_s c) hx

theorem ay_eq (c : Bool) {x : Nat} (hx : x < 64) : (modl c ()).ay[x]! = lk6 (tyT c) x :=
  tab_of (by norm_num) (ch441796_tab_y c) hx

private theorem iterA_eq {f : Array Nat} {F : Nat → Nat} (hf : ∀ x < 64, f[x]! = F x)
    (hF : ∀ x, F x < 64) (k : Nat) {u : Nat} (hu : u < 64) :
    iterA f k u = itN F k u ∧ itN F k u < 64 := by
  induction k with
  | zero => exact ⟨rfl, hu⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    change f[iterA f k u]! = F (itN F k u) ∧ F (itN F k u) < 64
    rw [h1, hf _ h2]
    exact ⟨rfl, hF _⟩

theorem act_eq (c : Bool) {w u : Nat} (hw : w < 16) (hu : u < 64) :
    (modl c ()).act w u = actL c w u := by
  unfold Mod.act
  have hy := iterA_eq (fun x hx => ay_eq c hx) (lk6_lt _) (w / 8) hu
  have hs := iterA_eq (fun x hx => as_eq c hx) (lk6_lt _) (w / 4 % 2) hy.2
  have hq := iterA_eq (fun x hx => aq_eq c hx) (lk6_lt _) (w % 4) hs.2
  rw [hy.1, hs.1, hq.1]
  have h := (allN_iff 64 _).mp ((allN_iff 16 _).mp (ch441796_act c) w hw) u hu
  exact (Nat.eq_of_beq_eq_true h).symm

theorem uMulP_eq {x y : Nat} (hx : x < 64) (hy : y < 64) : uMulP x y = uMul x y :=
  Nat.eq_of_beq_eq_true ((allN_iff 64 _).mp ((allN_iff 64 _).mp ch441796_umul x hx) y hy)

theorem amulL_eq {w v : Nat} (hw : w < 16) (hv : v < 16) : amulL w v = amul w v :=
  Nat.eq_of_beq_eq_true ((allN_iff 16 _).mp ((allN_iff 16 _).mp ch441796_amul w hw) v hv)

theorem actL_lt (c : Bool) (w u : Nat) : actL c w u < 64 :=
  Nat.lt_of_le_of_lt (Nat.and_le_right) (by norm_num)

theorem fzbMul_eq (c : Bool) {x y : Nat} (hx : x < 1024) (hy : y < 1024) :
    fzbMul c x y = mulN c x y := by
  rw [fzb_mul_eq_mulA]
  have e1 : ∀ z : Nat, Nat.land z 63 = z % 64 := fun z => by
    have h := Nat.and_two_pow_sub_one_eq_mod z 6
    norm_num at h
    exact h
  have e2 : ∀ z : Nat, Nat.shiftRight z 6 = z / 64 := fun z => by
    have h := Nat.shiftRight_eq_div_pow z 6
    norm_num at h
    exact h
  have e3 : ∀ z : Nat, Nat.shiftLeft z 6 = z * 64 := fun z => by
    have h := Nat.shiftLeft_eq z 6
    norm_num at h
    exact h
  have hxw : x / 64 < 16 := by omega
  have hyw : y / 64 < 16 := by omega
  have hxu : x % 64 < 64 := Nat.mod_lt _ (by norm_num)
  have hyu : y % 64 < 64 := Nat.mod_lt _ (by norm_num)
  change uMul (x % 64) ((modl c ()).act (x / 64) (y % 64)) + 64 * amul (x / 64) (y / 64) =
    Nat.add (uMulP (Nat.land x 63) (actL c (Nat.shiftRight x 6) (Nat.land y 63)))
      (Nat.shiftLeft (amulL (Nat.shiftRight x 6) (Nat.shiftRight y 6)) 6)
  rw [e1, e1, e2, e2, e3, act_eq c hxw hyu, uMulP_eq hxu (actL_lt _ _ _), amulL_eq hxw hyw,
    Nat.add_eq, Nat.mul_comm]

end CFSG.KC.FzBMod
