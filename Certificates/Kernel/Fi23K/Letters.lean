module

public import Certificates.Kernel.Fi23K.Facts
public import Certificates.Kernel.Fi23K.Orb
public import CFSG.Certificates.Kernel.Fi23K.WordSound
public import CFSG.Certificates.Kernel.Spor.TabWords
import CFSG.Certificates.Kernel.Spor.RawOrbEval
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23K

open CFSG.KC.Fi23K CFSG.KS.TW CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

@[expose] def hdEq (r : Nat) : Nat :=
  if r < 10 then r else if r ≤ 38 then r + 55 else if r = 39 then 94 else if r = 40 then 95
  else if r = 41 then 96 else if r = 42 then 136 else if r = 43 then 137
  else if r ≤ 47 then r + 11 else if r ≤ 51 then r + 12
  else if r ≤ 75 then (if r % 2 = 0 then 124 + (r - 52) / 2 else 97 + (r - 53) / 2) else r + 33

theorem hd_ok : ∀ r < 91, hdEq r < 150 ∧ (EL (hdEq r)).head? = some r := by
  decide +kernel

theorem tb_lt (G : Nat → Nat) (r x : Nat) : tb G r x < 32768 := by
  unfold tb
  rw [CFSG.KS.Raw.Orb.strictN_eq]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

theorem rng : ∀ r < 91, ∀ x < 31671, tb G r x < 31671 := by
  intro r hr x hx
  obtain ⟨h1, h2⟩ := hd_ok r hr
  have h := (eq_all _ h1 x hx).1
  cases e : EL (hdEq r) with
  | nil => rw [e] at h2; simp at h2
  | cons a t =>
    rw [e] at h2
    simp only [List.head?_cons, Option.some.injEq] at h2
    subst h2
    exact h a t e

@[expose] noncomputable def rhsF (r : Nat) : Option (List Nat) :=
  if 10 ≤ r ∧ r ≤ 38 then some (ER (r + 55)) else if 76 ≤ r ∧ r ≤ 90 then some (ER (r + 33))
  else none

theorem rules_data : ∀ r < 91, (10 ≤ r ∧ r ≤ 38 → EL (r + 55) = [r] ∧ ∀ s ∈ ER (r + 55), s < 91) ∧
    (76 ≤ r ∧ r ≤ 90 → EL (r + 33) = [r] ∧ ∀ s ∈ ER (r + 33), s < 91) := by
  decide +kernel

theorem rule_ok : ∀ r u, rhsF r = some u → (∀ s ∈ u, s < 91) ∧ ∀ x < 31671, tb G r x = wv G u x := by
  intro r u hu
  unfold rhsF at hu
  split_ifs at hu with h1 h2
  · cases hu
    obtain ⟨hl, hs⟩ := (rules_data r (by omega)).1 h1
    refine ⟨hs, fun x hx => ?_⟩
    have := (eq_all (r + 55) (by omega) x hx).2
    rw [hl] at this
    exact this
  · cases hu
    obtain ⟨hl, hs⟩ := (rules_data r (by omega)).2 h2
    refine ⟨hs, fun x hx => ?_⟩
    have := (eq_all (r + 33) (by omega) x hx).2
    rw [hl] at this
    exact this

theorem expand (f : Nat) {w : List Nat} (hw : ∀ r ∈ w, r < 91) {x : Nat} (hx : x < 31671) :
    wv G w x = wv G (exW rhsF f w) x :=
  exW_eq rng rule_ok f w hw x hx

theorem eqv {k : Nat} (hk : k < 150) {x : Nat} (hx : x < 31671) : wv G (EL k) x = wv G (ER k) x :=
  (eq_all k hk x hx).2

theorem tr_congr {n : Nat} {t : Table} {f g : Nat → Nat} (h : CFSG.KS.TW.TR n t f)
    (hfg : ∀ i < n, f i = g i) : CFSG.KS.TW.TR n t g :=
  ⟨h.1, fun i hi => by rw [← hfg i hi]; exact h.2 i hi⟩

theorem right_inv_of_left {n : Nat} {f g : Nat → Nat} (hf : ∀ x < n, f x < n) (hg : ∀ x < n, g x < n)
    (hgf : ∀ x < n, g (f x) = x) : ∀ y < n, f (g y) = y := by
  intro y hy
  let F : Fin n → Fin n := fun i => ⟨f i, hf i i.isLt⟩
  have hinj : Function.Injective F := by
    intro a b e
    have e' : f a = f b := congrArg Fin.val e
    have := congrArg g e'
    rw [hgf a a.isLt, hgf b b.isLt] at this
    exact Fin.ext this
  obtain ⟨a, ha⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨y, hy⟩
  have e : f a = y := congrArg Fin.val ha
  rw [← e, hgf a a.isLt]

theorem tabList_length (r : Nat) : ∀ c j, (tabList r j c).length = c
  | 0, _ => rfl
  | c + 1, j => by simp [tabList, tabList_length r c]

theorem tabList_getElem (r : Nat) : ∀ c j i (h : i < (tabList r j c).length),
    (tabList r j c)[i] = UInt32.ofNat (tb G r (j + i))
  | 0, _, i, h => by simp [tabList] at h
  | c + 1, j, 0, _ => by simp [tabList]
  | c + 1, j, i + 1, h => by
    simp only [tabList, List.getElem_cons_succ]
    rw [tabList_getElem r c (j + 1) i]
    congr 2
    omega

theorem tabOf_size (r : Nat) : (tabOf r).size = 31671 := by
  simp [tabOf, tabList_length]

theorem ap_tabOf (r : Nat) {x : Nat} (hx : x < 31671) : ap (tabOf r) x = tb G r x := by
  have hs : x < (tabOf r).size := by rw [tabOf_size]; exact hx
  unfold ap
  rw [getElem!_pos _ x hs]
  have e : (tabOf r)[x]'hs = UInt32.ofNat (tb G r (0 + x)) :=
    tabList_getElem r 31671 0 x (by rw [tabList_length]; exact hx)
  rw [e, Nat.zero_add, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_trans (tb_lt G r x) (by norm_num))

theorem tabOf_TR {r : Nat} (hr : r < 91) : CFSG.KS.TW.TR 31671 (tabOf r) (tb G r) :=
  ⟨tabOf_size r, fun i hi => ⟨ap_tabOf r hi, rng r hr i hi⟩⟩

@[expose] def regZ (z : Int) : Nat :=
  if z = 1 ∨ z = -1 then 39 else if z = 2 then 40 else if z = -2 then 41
  else if 0 < z then 52 + 2 * (z.natAbs - 3) else 53 + 2 * (z.natAbs - 3)

theorem binv_left {x : Nat} (hx : x < 31671) : tb G 41 (tb G 40 x) = x := by
  have h := eqv (k := 96) (by norm_num) hx
  have e1 : EL 96 = [41, 40] := by decide +kernel
  have e2 : ER 96 = [] := by decide +kernel
  rw [e1, e2] at h
  exact h

theorem binv_right {x : Nat} (hx : x < 31671) : tb G 40 (tb G 41 x) = x :=
  right_inv_of_left (rng 40 (by norm_num)) (rng 41 (by norm_num)) (fun _ h => binv_left h) x hx

theorem genTables_TR {z : Int} (hz : z.natAbs ≤ 2) (hz0 : z ≠ 0) :
    CFSG.KS.TW.TR 31671 (genTables orbLit z) (tb G (regZ z)) := by
  have hz' : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
  rcases hz' with rfl | rfl | rfl | rfl
  · exact tabOf_TR (by norm_num)
  · exact tabOf_TR (by norm_num)
  · exact tabOf_TR (by norm_num)
  · have e : genTables orbLit (-2) = invT 31671 (tabOf 40) := rfl
    rw [e]
    exact invT_TR (by norm_num) (tabOf_TR (by norm_num)) fun i hi =>
      ⟨rng 41 (by norm_num) i hi, binv_right hi, binv_left hi⟩

theorem foldr_regZ (w : List Int) (x : Nat) :
    w.foldr (fun z y => tb G (regZ z) y) x = wv G (w.map regZ) x := by
  induction w with
  | nil => rfl
  | cons z w ih => rw [List.foldr_cons, ih, List.map_cons, wv_cons]

theorem words_data : (chainWords ()).size = 12 ∧ ∀ j < 12,
    (∀ z ∈ (chainWords ())[j]!, z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs - 3 < j)) ∧
    (∀ z ∈ (chainWords ())[j]!, regZ z < 91) ∧
    exW rhsF 20 (ER (124 + j)) = ((chainWords ())[j]!).map regZ ∧ (∀ s ∈ ER (124 + j), s < 91) ∧
    EL (124 + j) = [52 + 2 * j] ∧ EL (97 + j) = [53 + 2 * j, 52 + 2 * j] ∧ ER (97 + j) = [] := by
  decide +kernel

theorem letter_inv {j : Nat} (hj : j < 12) {x : Nat} (hx : x < 31671) :
    LL (2 * j + 1) (LL (2 * j) x) = x := by
  obtain ⟨-, hw⟩ := words_data
  obtain ⟨-, -, -, -, -, hIL, hIR⟩ := hw j hj
  have h := eqv (k := 97 + j) (by omega) hx
  rw [hIL, hIR] at h
  unfold LL
  have e1 : Nat.add 52 (2 * j + 1) = 53 + 2 * j := by
    change 52 + (2 * j + 1) = _
    omega
  rw [e1]
  exact h

theorem LL_lt {l : Nat} (hl : l < 24) {x : Nat} (hx : x < 31671) : LL l x < 31671 :=
  rng _ (by change 52 + l < 91; omega) x hx

@[expose] def LInv (j : Nat) (L : Array Table) : Prop :=
  L.size = 2 * j ∧ ∀ l < 2 * j, CFSG.KS.TW.TR 31671 L[l]! (LL l)

theorem get!_push_lt {α : Type} [Inhabited α] (xs : Array α) (x : α) {i : Nat} (h : i < xs.size) :
    (xs.push x)[i]! = xs[i]! := by
  rw [getElem!_pos (xs.push x) i (by rw [Array.size_push]; omega), getElem!_pos xs i h,
    Array.getElem_push_lt h]

theorem get!_push_eq {α : Type} [Inhabited α] (xs : Array α) (x : α) : (xs.push x)[xs.size]! = x := by
  rw [getElem!_pos _ _ (by rw [Array.size_push]; omega), Array.getElem_push_eq]

theorem letter_step {j : Nat} (hj : j < 12) {L : Array Table} (H : LInv j L) :
    LInv (j + 1) (let T := wordT 31671 (slpLetterT (genTables orbLit) L) (chainWords ())[j]!
      (L.push T).push (invT 31671 T)) := by
  obtain ⟨-, hw⟩ := words_data
  obtain ⟨hz, hzr, hex, hER, hEL, hIL, hIR⟩ := hw j hj
  obtain ⟨hs, hL⟩ := H
  have hletter : ∀ z ∈ (chainWords ())[j]!,
      CFSG.KS.TW.TR 31671 (slpLetterT (genTables orbLit) L z) (tb G (regZ z)) := by
    intro z hzm
    obtain ⟨hz0, hzj⟩ := hz z hzm
    unfold slpLetterT
    by_cases h2 : z.natAbs ≤ 2
    · rw [if_pos h2]
      exact genTables_TR h2 hz0
    · rw [if_neg h2]
      have hj' : z.natAbs - 3 < j := by omega
      by_cases hp : 0 < z
      · rw [if_pos hp]
        have e : regZ z = 52 + 2 * (z.natAbs - 3) := by
          unfold regZ
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hp]
        rw [e]
        exact hL _ (by omega)
      · rw [if_neg hp]
        have e : regZ z = 53 + 2 * (z.natAbs - 3) := by
          unfold regZ
          rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hp]
        rw [e]
        have := hL (2 * (z.natAbs - 3) + 1) (by omega)
        unfold LL at this
        have e2 : Nat.add 52 (2 * (z.natAbs - 3) + 1) = 53 + 2 * (z.natAbs - 3) := by
          change 52 + (2 * (z.natAbs - 3) + 1) = _
          omega
        rw [e2] at this
        exact this
  have hT := wordT_TR (by norm_num) (chainWords ())[j]! hletter
  have hval : ∀ x < 31671, (chainWords ())[j]!.foldr (fun z y => tb G (regZ z) y) x = LL (2 * j) x := by
    intro x hx
    rw [foldr_regZ, ← hex, ← expand 20 hER hx, ← eqv (by omega) hx, hEL]
    unfold LL
    rfl
  have hT' := tr_congr hT hval
  have hinv : ∀ x < 31671, LL (2 * j + 1) (LL (2 * j) x) = x := by
    intro x hx
    have h := eqv (k := 97 + j) (by omega) hx
    rw [hIL, hIR] at h
    unfold LL
    have e1 : Nat.add 52 (2 * j + 1) = 53 + 2 * j := by
      change 52 + (2 * j + 1) = _
      omega
    rw [e1]
    exact h
  have hLr : ∀ l < 24, ∀ x < 31671, LL l x < 31671 := fun l hl x hx => rng _ (by
    change 52 + l < 91
    omega) x hx
  have hU := invT_TR (by norm_num) hT' (g := LL (2 * j + 1)) fun i hi =>
    ⟨hLr _ (by omega) i hi,
      right_inv_of_left (hLr _ (by omega)) (hLr _ (by omega)) hinv i hi, hinv i hi⟩
  dsimp only
  refine ⟨by rw [Array.size_push, Array.size_push, hs]; omega, fun l hl => ?_⟩
  rcases (by omega : l < 2 * j ∨ l = 2 * j ∨ l = 2 * j + 1) with h | rfl | rfl
  · rw [get!_push_lt _ _ (by rw [Array.size_push]; omega), get!_push_lt _ _ (by omega)]
    exact hL l h
  · rw [get!_push_lt _ _ (by rw [Array.size_push]; omega)]
    have h2 : (L.push (wordT 31671 (slpLetterT (genTables orbLit) L) (chainWords ())[j]!))[2 * j]! =
        wordT 31671 (slpLetterT (genTables orbLit) L) (chainWords ())[j]! := by
      rw [← hs]
      exact get!_push_eq _ _
    rw [h2]
    exact hT'
  · have e : 2 * j + 1 = (L.push (wordT 31671 (slpLetterT (genTables orbLit) L)
        (chainWords ())[j]!)).size := by rw [Array.size_push, hs]
    rw [e, get!_push_eq, ← e]
    exact hU

theorem letters_take : ∀ j ≤ 12, LInv j (((chainWords ()).toList.take j).foldl (fun L w =>
    let T := wordT 31671 (slpLetterT (genTables orbLit) L) w
    (L.push T).push (invT 31671 T)) #[])
  | 0, _ => ⟨rfl, fun l hl => absurd hl (by omega)⟩
  | j + 1, hj => by
    have hs : j < (chainWords ()).toList.length := by
      rw [Array.length_toList, words_data.1]
      omega
    rw [List.take_succ, List.getElem?_eq_getElem hs, Option.toList_some, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have e : (chainWords ()).toList[j] = (chainWords ())[j]! := by
      rw [Array.getElem_toList, getElem!_pos _ j (by rw [words_data.1]; omega)]
    rw [e]
    exact letter_step (by omega) (letters_take j (by omega))

theorem letters_TR : (chainLetters orbLit).size = 24 ∧
    ∀ l < 24, CFSG.KS.TW.TR 31671 (chainLetters orbLit)[l]! (LL l) := by
  have e : chainLetters orbLit = ((chainWords ()).toList.take 12).foldl (fun L w =>
      let T := wordT 31671 (slpLetterT (genTables orbLit) L) w
      (L.push T).push (invT 31671 T)) #[] := by
    have h12 : (chainWords ()).toList.take 12 = (chainWords ()).toList :=
      List.take_of_length_le (by rw [Array.length_toList, words_data.1])
    rw [h12, Array.foldl_toList]
    rfl
  rw [e]
  exact letters_take 12 le_rfl

end CFSG.KD.Fi23K

end
