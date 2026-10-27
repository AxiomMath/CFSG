module

public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Sporadic.J4.QTRankNative
public import CFSG.Certificates.Kernel.J4Q.RepQT
public import Certificates.Kernel.J4Q.X0

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q

@[expose] noncomputable def mkSet (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor ih (Nat.shiftLeft (nat_lit 1) x)) l

@[expose] noncomputable def mkNodupFrom (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih acc => andB (notB (bitB acc x)) (ih (Nat.lor acc (Nat.shiftLeft (nat_lit 1) x)))) l

@[expose] noncomputable def mkNodup (l : List Nat) : Bool := mkNodupFrom l (nat_lit 0)

theorem testBit_one_shiftLeft (x c : Nat) : (Nat.shiftLeft 1 x).testBit c = decide (x = c) := by
  change (1 <<< x).testBit c = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem mem_mkSet (c : Nat) : ∀ l : List Nat, c ∈ l ↔ (mkSet l).testBit c = true
  | [] => by
    change c ∈ [] ↔ (0 : Nat).testBit c = true
    simp
  | x :: l => by
    change _ ↔ (Nat.lor (mkSet l) (Nat.shiftLeft 1 x)).testBit c = true
    change _ ↔ ((mkSet l) ||| (Nat.shiftLeft 1 x)).testBit c = true
    rw [Nat.testBit_or, testBit_one_shiftLeft, List.mem_cons, mem_mkSet c l]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro (h | h)
      · exact Or.inr h.symm
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl h.symm

theorem mkNodupFrom_spec : ∀ (l : List Nat) (acc : Nat), mkNodupFrom l acc = true →
    l.Nodup ∧ ∀ x ∈ l, acc.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: l, acc, h => by
    obtain ⟨h1, h2⟩ := andB_true h
    obtain ⟨hn, hl⟩ := mkNodupFrom_spec l _ h2
    have hx : acc.testBit x = false := by
      rw [← bitB_eq]
      revert h1
      cases bitB acc x <;> decide
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hn⟩, ?_⟩
    · have := hl x hm
      change (acc ||| Nat.shiftLeft 1 x).testBit x = false at this
      rw [Nat.testBit_or, testBit_one_shiftLeft] at this
      simp at this
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hx
      · have := hl y hy
        change (acc ||| Nat.shiftLeft 1 x).testBit y = false at this
        rw [Nat.testBit_or] at this
        simp only [Bool.or_eq_false_iff] at this
        exact this.1

theorem nodup_of_mkNodup {l : List Nat} (h : mkNodup l = true) : l.Nodup :=
  (mkNodupFrom_spec l 0 h).1

theorem mem_of_mkSet_eq {l l' : List Nat} (h : Nat.beq (mkSet l) (mkSet l') = true) {c : Nat}
    (hc : c ∈ l') : c ∈ l := by
  rw [mem_mkSet] at hc ⊢
  rwa [Nat.eq_of_beq_eq_true h]

@[expose] noncomputable def actN (m : Nat) (t : List Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (getN (nat_lit 0) t j)) (bitB c j)) m

@[expose] noncomputable def fixFrom (t : List Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c cnt => Bool.rec (motive := fun _ => Nat) cnt (Nat.succ cnt) (Nat.beq (actN 11 t c) c)) n

@[expose] noncomputable def fixN (t : List Nat) : Nat := fixFrom t (nat_lit 2048)

theorem getN_zero_eq : ∀ (t : List Nat) (j : Nat), getN 0 t j = t.getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: t, j + 1 => getN_zero_eq t j

theorem rowsXor_eq (t : List Nat) (c : Nat) :
    ∀ m, CFSG.Sporadic.J4.QT.rowsXor (fun j => t.getD j 0) m c = actN m t c
  | 0 => rfl
  | m + 1 => by
    have ih := rowsXor_eq t c m
    unfold CFSG.Sporadic.J4.QT.rowsXor at ih ⊢
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    change _ = Bool.rec (motive := fun _ => Nat) (actN m t c) (Nat.xor (actN m t c) (getN 0 t m)) (bitB c m)
    rw [bitB_eq, getN_zero_eq]
    cases c.testBit m <;> rfl

theorem actT_eq (t : List Nat) (c : Nat) : CFSG.Sporadic.J4.QT.actT t c = actN 11 t c :=
  rowsXor_eq t c 11

theorem fixN_gen (t : List Nat) : ∀ n,
    fixFrom t n = ((List.range n).filter fun c => CFSG.Sporadic.J4.QT.actT t c == c).length
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.length_append, ← fixN_gen t n]
    change Bool.rec (motive := fun _ => Nat) (fixFrom t n) (Nat.succ (fixFrom t n))
      (Nat.beq (actN 11 t n) n) = _
    have e : (CFSG.Sporadic.J4.QT.actT t n == n) = Nat.beq (actN 11 t n) n := by
      rw [actT_eq, Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
    simp only [List.filter_cons, List.filter_nil, e]
    cases Nat.beq (actN 11 t n) n <;> rfl

theorem fixCount_eq (t : List Nat) : CFSG.Sporadic.J4.QT.fixCount t = fixN t := by
  unfold CFSG.Sporadic.J4.QT.fixCount fixN
  rw [fixN_gen]

theorem mem_eraseDups_nat : ∀ (n : Nat) (l : List Nat), l.length ≤ n → ∀ x, x ∈ l.eraseDups ↔ x ∈ l
  | 0, [], _, _ => Iff.rfl
  | n + 1, [], _, _ => Iff.rfl
  | 0, _ :: _, h, _ => absurd h (by simp)
  | n + 1, a :: as, h, x => by
    rw [List.eraseDups_cons, List.mem_cons, List.mem_cons,
      mem_eraseDups_nat n _ (le_trans (List.length_filter_le _ _) (by simpa using h)), List.mem_filter]
    by_cases hx : x = a
    · simp [hx]
    · simp [hx]

theorem contains_eraseDups (l : List Nat) (x : Nat) : l.eraseDups.contains x = bitB (mkSet l) x := by
  rw [bitB_eq, Bool.eq_iff_iff, ← mem_mkSet, List.contains_iff_mem, mem_eraseDups_nat _ l le_rfl]

theorem act_eq (ℓ : Int) (c : Nat) : CFSG.Sporadic.J4.QT.act ℓ c =
    actN 11 (CFSG.Sporadic.J4.QT.letterRows.getD (CFSG.Sporadic.J4.QT.letters.idxOf ℓ) []) c := by
  unfold CFSG.Sporadic.J4.QT.act CFSG.Sporadic.J4.QT.letterRow
  exact rowsXor_eq _ _ 11

@[expose] noncomputable def getL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun m _ ih i => Nat.rec (motive := fun _ => List Nat) m (fun j _ => ih j) i) l i

theorem getL_eq : ∀ (l : List (List Nat)) (i : Nat), getL l i = l.getD i []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getL_eq l i

@[expose] noncomputable def compN (t t' : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (actN 11 t x) ih) t'

theorem compT_eq (t : List Nat) : ∀ t' : List Nat, CFSG.Sporadic.J4.QT.compT t t' = compN t t'
  | [] => rfl
  | x :: t' => by
    change (x :: t').map (CFSG.Sporadic.J4.QT.actT t) = actN 11 t x :: compN t t'
    rw [List.map_cons, actT_eq, ← compT_eq t t']
    rfl

theorem mkLt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem mkSplitW (w e : Nat) : w * (e / w) + e % w = e := Nat.div_add_mod e w

theorem mkChunkW {w n : Nat} {f : Nat → Nat → Bool} (h : ∀ k < n, CFSG.KC.Enum.allN w (f k) = true)
    {e : Nat} (he : e < w * n) : f (e / w) (e % w) = true :=
  CFSG.KS.allN_spec (h (e / w) (Nat.div_lt_of_lt_mul he)) (e % w)
    (Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 => by simp [h0] at he))

theorem mkSplit (e : Nat) : 32 * (e / 32) + e % 32 = e := Nat.div_add_mod e 32

theorem mkChunk {n : Nat} {f : Nat → Nat → Bool} (h : ∀ k < n, CFSG.KC.Enum.allN 32 (f k) = true)
    {e : Nat} (he : e < 32 * n) : f (e / 32) (e % 32) = true :=
  CFSG.KS.allN_spec (h (e / 32) (Nat.div_lt_of_lt_mul he)) (e % 32) (Nat.mod_lt _ (by decide))

end CertificateChecks.KernelJ4Q

end
