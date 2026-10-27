module

public import CFSG.Certificates.Kernel.YModel.Sound
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Bitwise
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.YModel

theorem decChunkC_eq (len : Nat) : ∀ (N : Nat) (t : List Nat),
    decChunkC len N (t.map Char.ofNat) = (decChunk len N t).map Char.ofNat := by
  induction len with
  | zero => intro N t; rfl
  | succ len ih =>
    intro N t
    change List.cons _ (decChunkC len _ _) = (List.cons _ (decChunk len _ _)).map Char.ofNat
    rw [ih, List.map_cons]

theorem charsOf_eq (L : List (Nat × Nat)) : charsOf L = (bytesOf L).map Char.ofNat := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨N, len⟩ := p
    change decChunkC len N (charsOf L) = (decChunk len N (bytesOf L)).map Char.ofNat
    rw [ih, decChunkC_eq]

theorem linesA_congr {n n' : Nat → Nat} {w lines : Nat} {F : Nat → Nat}
    (h : ∀ L < lines, n L = n' L) : linesA n w F lines = linesA n' w F lines := by
  unfold linesA
  congr 1
  apply List.map_congr_left
  intro L hL
  rw [h L (List.mem_range.mp hL)]

theorem linesA_congrF {n : Nat → Nat} {w lines : Nat} {F F' : Nat → Nat}
    (h : ∀ L < lines, F L = F' L) : linesA n w F lines = linesA n w F' lines := by
  unfold linesA
  congr 1
  apply List.map_congr_left
  intro L hL
  rw [h L (List.mem_range.mp hL)]

theorem linesA_select {n w lines : Nat} {F : Nat → Nat} (σ : List Nat) (hσ : ∀ c ∈ σ, c < lines) :
    (σ.map fun c => (linesA (fun _ => n) w F lines)[c]!).toArray =
      linesA (fun _ => n) w (fun c => F (σ.getD c 0)) σ.length := by
  unfold linesA
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ (by simpa using h2)]
    have := hσ _ (List.getElem_mem (by simpa using h1))
    simp [this]

theorem relsOK_of_weqK {k m : Nat} {Nf : Nat → Nat} {rels : List (List Nat)}
    (h : ∀ r ∈ rels, weqK k m Nf r [] = true) : relsOK k m Nf rels = true := by
  induction rels with
  | nil => rfl
  | cons r rs ih =>
    have h1 : Nat.beq (wordAp k m Nf r (MonsterConv.Perm.idP k)) (MonsterConv.Perm.idP k) = true :=
      h r List.mem_cons_self
    have h2 := ih fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    change andB (Nat.beq (wordAp k m Nf r (MonsterConv.Perm.idP k)) (MonsterConv.Perm.idP k))
      (relsOK k m Nf rs) = true
    rw [h1, h2]
    rfl

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem andB_eq_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem transOK_point {k w b lo hi a0 cnt : Nat} {U TT : Nat → Nat}
    (h : transOK k w U TT b lo hi a0 cnt = true) :
    ∀ a, a0 ≤ a → a < a0 + cnt → transOK k w U TT b lo hi a 1 = true := by
  induction cnt with
  | zero => intro a h1 h2; omega
  | succ c ih =>
    have h' := andB_eq_true h
    intro a h1 h2
    rcases Nat.lt_or_ge a (a0 + c) with h3 | h3
    · exact ih h'.2 a h1 h3
    · have e : a = a0 + c := by omega
      subst e
      change andB ((fun t => andB (codesIn w lo hi (ptP t) (ptL t))
        (mapsTo k w U (ptP t) (ptL t) b (ptX t))) (TT (Nat.add a0 c))) true = true
      rw [h'.1]
      rfl

theorem schOK_gen {k w Z lo hi top a0 cnt : Nat} {U TT : Nat → Nat} :
    ∀ (recs : List Nat) (r0 : Nat),
      List.rec (motive := fun _ => Nat → Bool)
        (fun r => Nat.beq r (Nat.mul cnt (Nat.sub hi lo)))
        (fun rec _ ih r => andB (Nat.blt r (Nat.mul cnt (Nat.sub hi lo)))
          (andB (recOK k w U TT Z hi top (Nat.add a0 (Nat.div r (Nat.sub hi lo)))
              (Nat.add lo (Nat.mod r (Nat.sub hi lo))) rec)
            (strictB (Nat.succ r) ih)))
        recs r0 = true →
      r0 + recs.length = cnt * (hi - lo) ∧ ∀ r, r0 ≤ r → r < r0 + recs.length →
        ∃ rec, recOK k w U TT Z hi top (a0 + r / (hi - lo)) (lo + r % (hi - lo)) rec = true := by
  intro recs
  induction recs with
  | nil =>
    intro r0 h
    refine ⟨?_, fun r h1 h2 => by simp at h2; omega⟩
    simpa using Nat.eq_of_beq_eq_true h
  | cons rec rs ih =>
    intro r0 h
    have h1 := andB_eq_true h
    have h2 := andB_eq_true h1.2
    have h3 : List.rec (motive := fun _ => Nat → Bool)
        (fun r => Nat.beq r (Nat.mul cnt (Nat.sub hi lo)))
        (fun rec _ ih r => andB (Nat.blt r (Nat.mul cnt (Nat.sub hi lo)))
          (andB (recOK k w U TT Z hi top (Nat.add a0 (Nat.div r (Nat.sub hi lo)))
              (Nat.add lo (Nat.mod r (Nat.sub hi lo))) rec)
            (strictB (Nat.succ r) ih)))
        rs (r0 + 1) = true := h2.2
    obtain ⟨e, hr⟩ := ih (r0 + 1) h3
    refine ⟨by simp only [List.length_cons]; omega, fun r h4 h5 => ?_⟩
    rcases Nat.lt_or_ge r0 r with h6 | h6
    · exact hr r (by omega) (by simp only [List.length_cons] at h5; omega)
    · have e2 : r = r0 := by omega
      subst e2
      exact ⟨rec, h2.1⟩

theorem schOK_rec {k w Z lo hi top a0 cnt : Nat} {U TT : Nat → Nat} {recs : List Nat}
    (h : schOK k w U TT Z lo hi top a0 cnt recs = true) (hlo : lo < hi) :
    ∀ a, a0 ≤ a → a < a0 + cnt → ∀ j, lo ≤ j → j < hi →
      ∃ rec, recOK k w U TT Z hi top a j rec = true := by
  obtain ⟨e, hr⟩ := schOK_gen recs 0 h
  intro a h1 h2 j h3 h4
  have hd : 0 < hi - lo := by omega
  have hlt : (hi - lo) * (a - a0) + (j - lo) < 0 + recs.length := by
    rw [e]
    have : (hi - lo) * (a - a0) + (j - lo) < (hi - lo) * (a - a0 + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc _ < (hi - lo) * (a - a0 + 1) := this
      _ ≤ (hi - lo) * cnt := Nat.mul_le_mul_left _ (by omega)
      _ = cnt * (hi - lo) := Nat.mul_comm _ _
  have := hr ((hi - lo) * (a - a0) + (j - lo)) (by omega) hlt
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt (by omega), Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (by omega)] at this
  rwa [show a0 + (a - a0) = a by omega, show lo + (j - lo) = j by omega] at this

theorem size_linesA (n : Nat → Nat) (w : Nat) (F : Nat → Nat) (lines : Nat) :
    (linesA n w F lines).size = lines := by
  simp [linesA]

theorem forall_mem_of_lgetL {P : List Nat → Prop} {l : List (List Nat)}
    (h : ∀ i < l.length, P (lgetL l i)) : ∀ r ∈ l, P r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact h 0 (by simp)
    · exact ih (fun i hi => h (i + 1) (by simp only [List.length_cons]; omega)) r hr

theorem extract_linesA {n : Nat → Nat} {w lines j : Nat} {F : Nat → Nat} (h : j ≤ lines) :
    (linesA n w F lines).extract 0 j = linesA n w F j := by
  apply Array.ext
  · simp [linesA]; omega
  · intro i hi1 hi2
    simp [linesA] at hi1 hi2 ⊢

theorem getElem!_linesA {n : Nat → Nat} {w lines c : Nat} {F : Nat → Nat} (h : c < lines) :
    (linesA n w F lines)[c]! = unpackA (n c) w (F c) := by
  simp [linesA, h]

theorem getElem!_unpackA {n w F i : Nat} (h : i < n) : (unpackA n w F)[i]! = fieldAt w F i := by
  simp [unpackA, h]

theorem fieldAt_eq (w X i : Nat) : fieldAt w X i = (X >>> (w * i)) % 2 ^ w := by
  change (X >>> (w * i)) &&& ((1 <<< w) - 1) = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.and_two_pow_sub_one_eq_mod]

theorem fieldAt_signExt {n F i : Nat} (hF : F < 2 ^ (32 * n)) (hn : n + 1 < 2 ^ 32) :
    fieldAt 32 (signExt n F) i =
      if i < n then fieldAt 32 F i else if i = n then n + 1 else if i = n + 1 then n else 0 := by
  have hn' : n < 2 ^ 32 := by omega
  rw [fieldAt_eq, fieldAt_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow]
  unfold signExt
  simp only [Nat.testBit_shiftRight]
  by_cases hj : j < 32
  · simp only [hj, decide_true, Bool.true_and]
    split_ifs with h1 h2 h3
    · rw [Nat.testBit_mod_two_pow]
      simp only [hj, decide_true, Bool.true_and]
      have a1 : ¬ 32 * n ≤ 32 * i + j := by omega
      have a2 : ¬ 32 * (n + 1) ≤ 32 * i + j := by omega
      simp [a1, a2]
    · subst h2
      have hb : F.testBit (32 * i + j) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hF (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have a2 : ¬ 32 * (i + 1) ≤ 32 * i + j := by omega
      simp [hb, a2]
    · subst h3
      have hb : F.testBit (32 * (n + 1) + j) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hF (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hb2 : (n + 1).testBit (32 * (n + 1) + j - 32 * n) = false := by
        apply Nat.testBit_eq_false_of_lt
        exact lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [hb, hb2, show 32 * n ≤ 32 * (n + 1) + j by omega]
    · have hb : F.testBit (32 * i + j) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hF (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have hb2 : (n + 1).testBit (32 * i + j - 32 * n) = false := by
        apply Nat.testBit_eq_false_of_lt
        exact lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega))
      have hb3 : n.testBit (32 * i + j - 32 * (n + 1)) = false := by
        apply Nat.testBit_eq_false_of_lt
        exact lt_of_lt_of_le hn' (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [hb, hb2, hb3]
  · have key : ∀ x < 2 ^ 32, x.testBit j = false := fun x hx =>
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp only [hj, decide_false, Bool.false_and]
    symm
    split_ifs
    · exact key _ (Nat.mod_lt _ (by norm_num))
    · exact key _ hn
    · exact key _ hn'
    · exact key _ (by norm_num)

theorem withSign_linesA {n m : Nat} {F : Nat → Nat} (h : ∀ c < m, F c < Nat.shiftLeft 1 (32 * n))
    (hn : n + 1 < 2 ^ 32) :
    CFSG.YGroups.ModelNative.withSign (linesA (fun _ => n) 32 F m) =
      linesA (fun _ => n + 2) 32 (fun c => signExt n (F c)) m := by
  unfold CFSG.YGroups.ModelNative.withSign linesA
  rw [List.map_toArray, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  have hF : F c < 2 ^ (32 * n) := by
    have : F c < 1 <<< (32 * n) := h c (List.mem_range.mp hc)
    rwa [Nat.shiftLeft_eq, one_mul] at this
  simp only [Function.comp_apply]
  apply Array.ext
  · simp [unpackA]
  · intro i hi1 hi2
    simp only [unpackA, Array.size_ofFn, Array.size_push] at hi1 hi2
    unfold unpackA
    simp only [Array.getElem_ofFn, fieldAt_signExt hF hn, Array.getElem_push, Array.size_ofFn,
      Array.size_push]
    rcases (show i < n ∨ i = n ∨ i = n + 1 by omega) with h1 | h1 | h1
    · simp [h1, show i < n + 1 by omega]
    · subst h1
      simp
    · subst h1
      simp

end CFSG.KC.YModel

end
