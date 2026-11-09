module

public import Certificates.Kernel.Sporadic.Fi24F4.JC
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound
public import CFSG.Certificates.Kernel.Spor.Fi24FixPSound
import CFSG.Certificates.Kernel.Common.SliceRange
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.IntervalCases

set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24F4.JXs TT "Certificates/Kernel/Sporadic/Fi24F4/data/jxt.bin" 65536 4 4980736 5736814539445380799

namespace CFSG.KD.Fi24F4.JXs

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24R2W CFSG.KC.Fi24F4J CFSG.KC.Fi24NetPt CFSG.KD.Fi24Net
  CFSG.KD.Fi24F4

public theorem walkN_cons (NW : Nat → Nat → Nat) (l : Nat) (w : List Nat) (x : Nat) :
    walkN NW (l :: w) x = walkN NW w (letN NW l x) := by
  change CFSG.KC.Loop.strictN _ _ = _
  generalize letN NW l x = y
  cases y <;> rfl

public theorem walkN_append (NW : Nat → Nat → Nat) (u v : List Nat) :
    ∀ x, walkN NW (u ++ v) x = walkN NW v (walkN NW u x) := by
  induction u with
  | nil => intro x; rfl
  | cons l u ih => intro x; rw [List.cons_append, walkN_cons, walkN_cons, ih]

@[expose] public noncomputable def imgN (T : Nat → Nat) (x n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight (T k) x) (nat_lit 1)) k)) n

theorem testBit_imgN (T : Nat → Nat) (x : Nat) :
    ∀ n i, (imgN T x n).testBit i = (decide (i < n) && (T i).testBit x)
  | 0, i => by
    change (0 : Nat).testBit i = _
    simp
  | n + 1, i => by
    change ((imgN T x n) ||| (((T n >>> x) &&& 1) <<< n)).testBit i = _
    rw [Nat.testBit_or, testBit_imgN T x n i, Nat.testBit_shiftLeft, Nat.testBit_and,
      Nat.testBit_shiftRight]
    rcases Nat.lt_trichotomy i n with h | h | h
    · have h1 : ¬ i ≥ n := by omega
      simp [h, h1, Nat.lt_succ_of_lt h]
    · subst h
      simp
    · have h1 : ¬ i < n := by omega
      have h2 : ¬ i < n + 1 := by omega
      obtain ⟨j, hj⟩ : ∃ j, i - n = j + 1 := ⟨i - n - 1, by omega⟩
      have h4 : Nat.testBit 1 (i - n) = false := by
        rw [hj, Nat.testBit_succ]
        simp
      simp [h1, h2, h4]

public theorem imgN_lt (T : Nat → Nat) (x : Nat) : imgN T x 19 < 524288 := by
  apply Nat.lt_pow_two_of_testBit (n := 19)
  intro i hi
  rw [testBit_imgN, decide_eq_false (by omega), Bool.false_and]

theorem walkN_foldr (w : List Nat) :
    ∀ x, walkN NW w.reverse x = w.foldr (CFSG.KS.Fi24Net.LN NW) x := by
  induction w with
  | nil => intro x; rfl
  | cons l w ih =>
    intro x
    rw [List.reverse_cons, walkN_append, ih, List.foldr_cons, walkN_cons]
    exact CFSG.KS.Fi24NetPt.letN_eq NW l _

theorem nvAll : ∀ j, j < 13 → CFSG.KS.Fi24Net.NV (NW j) := by
  intro j hj
  interval_cases j <;> exact CFSG.KS.Fi24Net.nv_of_masksOK (by quickRfl)

theorem ln_lt {l : Nat} (hl : l < 26) {q : Nat} (hq : q < 524288) :
    CFSG.KS.Fi24Net.LN NW l q < 524288 := by
  unfold CFSG.KS.Fi24Net.LN
  split
  · exact CFSG.KS.Fi24Net.pF_lt (nvAll _ (by omega)) hq
  · exact CFSG.KS.Fi24Net.pR_lt (nvAll _ (by omega)) hq

theorem tab_spec {X : List Nat} {T : Nat → Nat} (hX : ∀ l ∈ X, l < 26)
    (hT : ∀ k < 19, T k = Fi24FixP.walkP (planeL NW) X (Fi24FixP.idPl19 k)) :
    ∀ x < 524288, walkN NW X.reverse x = imgN T x 19 := by
  intro x hx
  rw [walkN_foldr]
  have hσ : ∀ l ∈ X, ∀ q, q < 524288 → CFSG.KS.Fi24Net.LN NW l q < 524288 :=
    fun l hl _ hq => ln_lt (hX l hl) hq
  have hA : ∀ l ∈ X, ∀ v q, q < 524288 →
      (planeL NW l v).testBit q = v.testBit (CFSG.KS.Fi24Net.LN NW l q) :=
    fun l hl v q _ => CFSG.KS.Fi24NetPt.testBit_planeL (nvAll _ (by have := hX l hl; omega)) v q
  have hg := CFSG.KS.Fi24FixP.foldr_lt X hσ x hx
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_imgN]
  by_cases hi : i < 19
  · rw [decide_eq_true hi, Bool.true_and, hT i hi, CFSG.KS.Fi24FixP.testBit_walkP X hσ hA _ x hx,
      CFSG.KS.Fi24FixP.testBit_idPl19 hi, decide_eq_true hg, Bool.true_and]
  · rw [decide_eq_false hi, Bool.false_and]
    have h19 : (524288 : Nat) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_lt hi)
    exact Nat.testBit_lt_two_pow (by omega)

@[expose] public noncomputable def tw (t : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) SA (fun k _ => Nat.rec (motive := fun _ => List Nat) SB
    (fun j _ => Nat.rec (motive := fun _ => List Nat) (invC SA) (fun _ _ => invC SB) j) k) t

@[expose] public noncomputable def tab (t k : Nat) : Nat := TT (Nat.add (Nat.mul (nat_lit 19) t) k)

noncomputable def tabc (n : Nat) : Bool :=
  Nat.beq (TT n) (Fi24FixP.walkP (planeL NW) (tw (Nat.div n (nat_lit 19)))
    (Fi24FixP.idPl19 (Nat.mod n (nat_lit 19))))

#kc_slice_range tabc tb 0 76

theorem tab_of {t : Nat} (h : ∀ k < 19, tabc (Nat.add (Nat.mul 19 t) k) = true) :
    ∀ k < 19, tab t k = Fi24FixP.walkP (planeL NW) (tw t) (Fi24FixP.idPl19 k) := by
  intro k hk
  have e := Nat.eq_of_beq_eq_true (h k hk)
  have e1 : Nat.div (Nat.add (Nat.mul 19 t) k) 19 = t := by
    change (19 * t + k) / 19 = t
    omega
  have e2 : Nat.mod (Nat.add (Nat.mul 19 t) k) 19 = k := by
    change (19 * t + k) % 19 = k
    omega
  rw [e1, e2] at e
  exact e

public theorem tw_spec {t : Nat} (ht : t < 4) :
    ∀ x < 524288, walkN NW (tw t).reverse x = imgN (tab t) x 19 := by
  interval_cases t
  · refine tab_spec (by decide) (tab_of fun k hk => ?_)
    interval_cases k
    exacts [tb0, tb1, tb2, tb3, tb4, tb5, tb6, tb7, tb8, tb9, tb10, tb11, tb12, tb13, tb14, tb15,
      tb16, tb17, tb18]
  · refine tab_spec (by decide) (tab_of fun k hk => ?_)
    interval_cases k
    exacts [tb19, tb20, tb21, tb22, tb23, tb24, tb25, tb26, tb27, tb28, tb29, tb30, tb31, tb32,
      tb33, tb34, tb35, tb36, tb37]
  · refine tab_spec (by decide) (tab_of fun k hk => ?_)
    interval_cases k
    exacts [tb38, tb39, tb40, tb41, tb42, tb43, tb44, tb45, tb46, tb47, tb48, tb49, tb50, tb51,
      tb52, tb53, tb54, tb55, tb56]
  · refine tab_spec (by decide) (tab_of fun k hk => ?_)
    interval_cases k
    exacts [tb57, tb58, tb59, tb60, tb61, tb62, tb63, tb64, tb65, tb66, tb67, tb68, tb69, tb70,
      tb71, tb72, tb73, tb74, tb75]

@[expose] public noncomputable def gw (ix : Int → Nat) (w : List Int) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun z _ ih x => imgN (tab (ix z)) (ih x) (nat_lit 19)) w x

public theorem gw_lt (ix : Int → Nat) : ∀ (w : List Int) x, x < 524288 → gw ix w x < 524288
  | [], _, hx => hx
  | _ :: _, _, _ => imgN_lt _ _

public theorem gw_walk (ix : Int → Nat) (hix : ∀ z, ix z < 4) :
    ∀ (w : List Int) x, x < 524288 →
      walkN NW (w.foldr (fun z acc => tw (ix z) ++ acc) []).reverse x = gw ix w x
  | [], _, _ => rfl
  | z :: w, x, hx => by
    rw [List.foldr_cons, List.reverse_append, walkN_append, gw_walk ix hix w x hx]
    exact tw_spec (hix z) _ (gw_lt ix w x hx)

@[expose] public noncomputable def ti (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => Nat.rec (motive := fun _ => Nat) 1
      (fun k _ => Nat.rec (motive := fun _ => Nat) 0 (fun _ _ => 1) k) m)
    (fun m => Nat.rec (motive := fun _ => Nat) 2 (fun _ _ => 3) m) z

@[expose] public noncomputable def tiQ (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun m => Nat.rec (motive := fun _ => Nat) 1
      (fun k _ => Nat.rec (motive := fun _ => Nat) 0 (fun _ _ => 1) k) m) (fun _ => 1) z

public theorem ti_lt (z : Int) : ti z < 4 := by
  rcases z with (_ | _ | m) | (_ | m) <;> exact Nat.lt_of_sub_eq_succ rfl

public theorem tiQ_lt (z : Int) : tiQ z < 4 := by
  rcases z with (_ | _ | m) | m <;> exact Nat.lt_of_sub_eq_succ rfl

public theorem cw_eq : ∀ w : List Int, cw SA SB w = w.foldr (fun z acc => tw (ti z) ++ acc) []
  | [] => rfl
  | z :: w => by
    rw [List.foldr_cons, ← cw_eq w]
    rcases z with (_ | _ | m) | (_ | m) <;> rfl

public theorem cwQ_eq : ∀ w : List Int, cwQ SA SB w = w.foldr (fun z acc => tw (tiQ z) ++ acc) []
  | [] => rfl
  | z :: w => by
    rw [List.foldr_cons, ← cwQ_eq w]
    rcases z with (_ | _ | m) | m <;> rfl

@[expose] public noncomputable def stY (Y : List Nat) (f : Nat → Nat) : Bool :=
  Nat.beq (f 0) (walkN NW Y.reverse 0) && (Nat.beq (f 305530) (walkN NW Y.reverse 305530) &&
    (Nat.beq (f 5604) (walkN NW Y.reverse 5604) && (Nat.beq (f 221549) (walkN NW Y.reverse 221549) &&
    (Nat.beq (f 266275) (walkN NW Y.reverse 266275) &&
    (Nat.beq (f 186844) (walkN NW Y.reverse 186844) && true)))))

public theorem stage_tab {X Y : List Nat} {f : Nat → Nat}
    (hf : ∀ x < 524288, walkN NW X.reverse x = f x) (hY : stY Y f = true) :
    stageOK NW X Y = true := by
  unfold stY at hY
  unfold stageOK base
  simp only [List.all_cons, List.all_nil]
  rw [hf 0 (by norm_num), hf 305530 (by norm_num), hf 5604 (by norm_num), hf 221549 (by norm_num),
    hf 266275 (by norm_num), hf 186844 (by norm_num)]
  exact hY

public theorem stage_cw {w : List Int} {Y : List Nat} (h : stY Y (gw ti w) = true) :
    stageOK NW (cw SA SB w) Y = true := by
  refine stage_tab (fun x hx => ?_) h
  rw [cw_eq]
  exact gw_walk ti ti_lt _ x hx

end CFSG.KD.Fi24F4.JXs
