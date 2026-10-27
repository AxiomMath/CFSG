module

public import Certificates.Kernel.Misc.Asc81c.Lin
import CFSG.Monster.B.Co2.PermArr
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CertificateChecks.KernelAsc81c

open CFSG.Quasithin.Asc81c.Pf.Check CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def Good (n : Nat) (c : List Nat) : Prop := ∀ v ∈ c, v < 2 ^ n

@[expose] def stepV (c : List Nat) (i : Nat) (acc k : Nat) : Nat :=
  if i.testBit k then acc ^^^ c.getD k 0 else acc

theorem linV_eq (n : Nat) (c : List Nat) (i : Nat) :
    linV n c i = (List.range n).foldl (stepV c i) 0 := rfl

theorem getD_lt {n : Nat} {c : List Nat} (hc : Good n c) (k : Nat) : c.getD k 0 < 2 ^ n := by
  rw [List.getD_eq_getElem?_getD]
  cases h : c[k]? with
  | none => simpa using Nat.two_pow_pos n
  | some v => exact hc v (List.mem_of_getElem? h)

theorem fold_lt {n : Nat} {c : List Nat} (hc : Good n c) (i : Nat) :
    ∀ (l : List Nat) (acc : Nat), acc < 2 ^ n → l.foldl (stepV c i) acc < 2 ^ n
  | [], _, h => h
  | k :: l, acc, h => by
    rw [List.foldl_cons]
    refine fold_lt hc i l _ ?_
    unfold stepV
    split
    · exact Nat.xor_lt_two_pow h (getD_lt hc k)
    · exact h

theorem linV_lt {n : Nat} {c : List Nat} (hc : Good n c) (i : Nat) : linV n c i < 2 ^ n := by
  rw [linV_eq]
  exact fold_lt hc i _ 0 (Nat.two_pow_pos n)

theorem fold_xor (c : List Nat) (i j : Nat) : ∀ (l : List Nat) (a b : Nat),
    l.foldl (stepV c (i ^^^ j)) (a ^^^ b) = l.foldl (stepV c i) a ^^^ l.foldl (stepV c j) b
  | [], _, _ => rfl
  | k :: l, a, b => by
    simp only [List.foldl_cons]
    rw [← fold_xor c i j l]
    congr 1
    unfold stepV
    rw [Nat.testBit_xor]
    cases i.testBit k <;> cases j.testBit k <;> simp only [Bool.xor_true, Bool.xor_false,
      Bool.not_true, Bool.not_false, if_true, if_false, Bool.false_eq_true] <;>
      (apply Nat.eq_of_testBit_eq; intro m; simp only [Nat.testBit_xor];
        cases a.testBit m <;> cases b.testBit m <;> cases (c.getD k 0).testBit m <;> rfl)

theorem linV_xor (n : Nat) (c : List Nat) (i j : Nat) :
    linV n c (i ^^^ j) = linV n c i ^^^ linV n c j := by
  rw [linV_eq, linV_eq, linV_eq, ← fold_xor c i j, Nat.xor_self]

theorem fold_zero (c : List Nat) : ∀ (l : List Nat), l.foldl (stepV c 0) 0 = 0
  | [] => rfl
  | k :: l => by
    simp only [List.foldl_cons, stepV, Nat.zero_testBit, Bool.false_eq_true, if_false]
    exact fold_zero c l

theorem linV_zero (n : Nat) (c : List Nat) : linV n c 0 = 0 := by
  rw [linV_eq]
  exact fold_zero c _

theorem linV_basis (c : List Nat) : ∀ n k, linV n c (2 ^ k) = if k < n then c.getD k 0 else 0
  | 0, k => by simp [linV]
  | n + 1, k => by
    rw [linV_eq, List.range_succ, List.foldl_append, ← linV_eq, linV_basis c n k]
    simp only [List.foldl_cons, List.foldl_nil, stepV, Nat.testBit_two_pow]
    by_cases h : k < n
    · have h1 : k < n + 1 := by omega
      have h2 : k ≠ n := by omega
      simp [h, h1, h2]
    · by_cases h3 : k = n
      · subst h3
        simp
      · have h4 : ¬ k < n + 1 := by omega
        simp [h, h3, h4]

theorem fold_congr {c d : List Nat} {n : Nat} (i : Nat) (h : ∀ k < n, c.getD k 0 = d.getD k 0) :
    ∀ (l : List Nat), (∀ k ∈ l, k < n) → ∀ acc, l.foldl (stepV c i) acc = l.foldl (stepV d i) acc
  | [], _, _ => rfl
  | k :: l, hl, acc => by
    simp only [List.foldl_cons]
    have hk := h k (hl k List.mem_cons_self)
    unfold stepV
    rw [hk]
    exact fold_congr i h l (fun k' hk' => hl k' (List.mem_cons_of_mem _ hk')) _

theorem linV_congr {c d : List Nat} {n : Nat} (h : ∀ k < n, c.getD k 0 = d.getD k 0) (i : Nat) :
    linV n c i = linV n d i := by
  rw [linV_eq, linV_eq]
  exact fold_congr i h _ (fun k hk => List.mem_range.1 hk) 0

theorem getD_map0 (f : Nat → Nat) (hf : f 0 = 0) (l : List Nat) (k : Nat) :
    (l.map f).getD k 0 = f (l.getD k 0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> simp [hf]

theorem fold_cmp (n : Nat) (c d : List Nat) (i : Nat) : ∀ (l : List Nat) (acc : Nat),
    linV n c (l.foldl (stepV d i) acc) = l.foldl (stepV (d.map (linV n c)) i) (linV n c acc)
  | [], _ => rfl
  | k :: l, acc => by
    simp only [List.foldl_cons]
    rw [fold_cmp n c d i l]
    congr 1
    unfold stepV
    split
    · rw [linV_xor, getD_map0 _ (linV_zero n c)]
    · rfl

theorem linV_cmp (n : Nat) (c d : List Nat) (i : Nat) :
    linV n (cmpL n c d) i = linV n c (linV n d i) := by
  rw [linV_eq n d, fold_cmp, linV_zero, linV_eq n (cmpL n c d)]
  rfl

theorem good_cmp {n : Nat} {c : List Nat} (hc : Good n c) (d : List Nat) : Good n (cmpL n c d) := by
  intro v hv
  obtain ⟨u, -, rfl⟩ := List.mem_map.1 hv
  exact linV_lt hc u

theorem good_idL (n : Nat) : Good n (idL n) := by
  intro v hv
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
  exact Nat.pow_lt_pow_right (by decide) (List.mem_range.1 hk)

theorem good_powL {n : Nat} {c : List Nat} (hc : Good n c) : ∀ e, Good n (powL n c e)
  | 0 => good_idL n
  | _ + 1 => good_cmp hc _

theorem good_evalL {n : Nat} {a b : List Nat} (ha : Good n a) (hb : Good n b) :
    ∀ w, Good n (evalL n a b w)
  | [] => good_idL n
  | false :: _ => good_cmp ha _
  | true :: _ => good_cmp hb _

theorem good_conjL {n : Nat} {c : List Nat} (hc : Good n c) (x : List Nat) : Good n (conjL n c x) :=
  good_cmp hc _

theorem get_linA {n : Nat} {c : List Nat} {i : Nat} (hi : i < 2 ^ n) :
    (linA n c)[i]! = linV n c i := by
  rw [getElem!_pos (linA n c) i (by simpa [linA] using hi)]
  simp [linA]

theorem compA_lin {n : Nat} (c : List Nat) {d : List Nat} (hd : Good n d) :
    compA (2 ^ n) (linA n c) (linA n d) = linA n (cmpL n c d) := by
  apply Array.ext
  · simp [compA, linA]
  · intro i h1 h2
    have hi : i < 2 ^ n := by simpa [compA] using h1
    rw [← getElem!_pos _ i h1, ← getElem!_pos _ i h2]
    have e : (compA (2 ^ n) (linA n c) (linA n d))[i]! = (linA n c)[(linA n d)[i]!]! := by
      unfold compA
      rw [getElem!_pos _ i (by simpa using hi)]
      simp
    rw [e, get_linA (c := d) hi, get_linA (linV_lt hd i), get_linA hi, linV_cmp]

theorem eqA_lin {n : Nat} (c d : List Nat) :
    eqA (2 ^ n) (linA n c) (linA n d) = eqL n c d := by
  have e : eqA (2 ^ n) (linA n c) (linA n d) = allLt (2 ^ n) fun i => linV n c i == linV n d i := by
    unfold eqA
    rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, CFSG.Monster.B.Co2.allLt_iff]
    refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · rw [← get_linA hi, ← get_linA hi]
      exact h i hi
    · rw [get_linA hi, get_linA hi]
      exact h i hi
  rw [e, Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff]
  unfold eqL
  rw [List.all_eq_true]
  constructor
  · intro h k hk
    have hk' := List.mem_range.1 hk
    have := h (2 ^ k) (Nat.pow_lt_pow_right (by decide) hk')
    rw [beq_iff_eq, linV_basis, linV_basis, if_pos hk', if_pos hk'] at this
    simpa using this
  · intro h i _
    rw [beq_iff_eq]
    exact linV_congr (fun k hk => by simpa using h k (List.mem_range.2 hk)) i

section Id

variable {n : Nat} (hid : idA (2 ^ n) = linA n (idL n))
include hid

theorem powA_lin {c : List Nat} (hc : Good n c) :
    ∀ e, powA (2 ^ n) (linA n c) e = linA n (powL n c e)
  | 0 => hid
  | e + 1 => by
    rw [powA, powA_lin hc e, compA_lin c (good_powL hc e)]
    rfl

theorem evalWA_lin {a b : List Nat} (ha : Good n a) (hb : Good n b) :
    ∀ w, evalWA (2 ^ n) (linA n a) (linA n b) w = linA n (evalL n a b w)
  | [] => hid
  | false :: w => by
    rw [evalWA, evalWA_lin ha hb w, compA_lin a (good_evalL ha hb w)]
    rfl
  | true :: w => by
    rw [evalWA, evalWA_lin ha hb w, compA_lin b (good_evalL ha hb w)]
    rfl

theorem ord21A_lin {c : List Nat} (hc : Good n c) : ord21A (2 ^ n) (linA n c) = ord21L n c := by
  unfold ord21A ord21L
  rw [powA_lin hid hc, hid, eqA_lin]

theorem conjA_lin {c x : List Nat} (hc : Good n c) (hx : Good n x) :
    conjA (2 ^ n) (linA n c) (linA n x) = linA n (conjL n c x) := by
  unfold conjA conjL
  rw [powA_lin hid hc, compA_lin x (good_powL hc 20), compA_lin c (good_cmp hx _)]

theorem meet3_lin (x a b : List Nat) :
    meet3 (2 ^ n) (linA n x) (linA n a) (linA n b) = meet3L n x a b := by
  unfold meet3 meet3L
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, CFSG.Monster.B.Co2.allLt_iff]
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have := h i hi
    rwa [get_linA hi, get_linA hi, get_linA hi] at this
  · rw [get_linA hi, get_linA hi, get_linA hi]
    exact h i hi

theorem ptW_lin {x a b : List Nat} (hx : Good n x) (ha : Good n a) (hb : Good n b)
    (w₁ w₂ v : List Bool) :
    ptW (2 ^ n) (linA n x) (linA n a) (linA n b) w₁ w₂ v = ptWL n x a b w₁ w₂ v := by
  have g1 := good_evalL hx ha w₁
  have g2 := good_evalL hx hb w₂
  unfold ptW ptWL
  rw [evalWA_lin hid hx ha, evalWA_lin hid hx hb, ord21A_lin hid g1, ord21A_lin hid g2,
    conjA_lin hid g1 hx, conjA_lin hid g2 hx,
    compA_lin _ (good_conjL g2 x), compA_lin _ (good_conjL g1 x), eqA_lin,
    evalWA_lin hid (good_conjL g1 x) (good_conjL g2 x),
    ord21A_lin hid (good_evalL (good_conjL g1 x) (good_conjL g2 x) v)]

theorem pairT_lin {x a b : List Nat} (hx : Good n x) (ha : Good n a) (hb : Good n b) (r : Nat) :
    pairT (2 ^ n) (linA n x) (linA n a) (linA n b) r = pairTL n x a b r := by
  unfold pairT pairTL
  rw [meet3_lin hid, ptW_lin hid hx ha hb, evalWA_lin hid hx ha, eqA_lin]

theorem fixCount_lin (c : List Nat) : fixCount (2 ^ n) (linA n c) = fixCountL n c := by
  unfold fixCount fixCountL
  have e : (fun i : Fin (2 ^ n) => (linA n c)[i.val]! == i.val) =
      (fun i : Fin (2 ^ n) => linV n c i.val == i.val) := funext fun i => by rw [get_linA i.2]
  rw [e]

theorem pre1_lin {x c : List Nat} (hx : Good n x) (hc : Good n c) :
    pre1 n (linA n x) (linA n c) = pre1L n x c := by
  unfold pre1 pre1L ord3A lawsOK
  rw [powA_lin hid hc, hid, eqA_lin, fixCount_lin hid, compA_lin x hc, compA_lin c hx, eqA_lin]
  have e : (fun w => ord21A (2 ^ n) (evalWA (2 ^ n) (linA n x) (linA n c) w)) =
      (fun w => ord21L n (evalL n x c w)) := funext fun w => by
    rw [evalWA_lin hid hx hc, ord21A_lin hid (good_evalL hx hc w)]
  rw [e]

end Id

end CertificateChecks.KernelAsc81c

end
