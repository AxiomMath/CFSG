
module

public import CFSG.Monster.B.TwoA.Fischer.CertFixedInputs
public import Certificates.Kernel.MonsterB.IndCandGet
public import Certificates.Kernel.MonsterB.FischerTabs
public import CFSG.Certificates.Kernel.MonsterB.FischerKSound
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMonB.Fischer3066

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Binary.Native CFSG.KC.FischerK CertificateChecks.KernelMonB.IndCand
  CertificateChecks.KernelMonB.FischerTabs CFSG.KLie.CT

@[expose] def xorFoldR (k x : Nat) : Nat := x ^^^ (x >>> k)

@[expose] def par128 (x : Nat) : Nat :=
  xorFoldR 1 (xorFoldR 2 (xorFoldR 4 (xorFoldR 8 (xorFoldR 16 (xorFoldR 32 (xorFoldR 64 x)))))) &&& 1

theorem xorFoldR_shiftRight (a b k : Nat) : (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor, Nat.testBit_shiftRight]

theorem xorFoldR_xor (k a b : Nat) : xorFoldR k (a ^^^ b) = xorFoldR k a ^^^ xorFoldR k b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [xorFoldR, Nat.testBit_xor, Nat.testBit_shiftRight]
  cases a.testBit i <;> cases b.testBit i <;> cases a.testBit (k + i) <;>
    cases b.testBit (k + i) <;> rfl

theorem par128_xor (a b : Nat) : par128 (a ^^^ b) = par128 a ^^^ par128 b := by
  simp only [par128, xorFoldR_xor, Nat.and_xor_distrib_right]

theorem xor_log2_lt_of_log2_eq {a b : Nat} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.log2 = b.log2) :
    a ^^^ b = 0 ∨ (a ^^^ b).log2 < a.log2 := by
  rcases Nat.eq_zero_or_pos (a ^^^ b) with h0 | h0
  · exact Or.inl h0
  · right
    have key : ∀ c, c ≠ 0 → c / 2 ^ c.log2 = 1 := by
      intro c hc
      have h1 := Nat.log2_self_le hc
      have h2 := Nat.lt_log2_self (n := c)
      have hp : 0 < 2 ^ c.log2 := Nat.two_pow_pos _
      apply Nat.le_antisymm
      · have : c / 2 ^ c.log2 < 2 := by
          rw [Nat.div_lt_iff_lt_mul hp]
          rw [Nat.pow_succ] at h2
          omega
        omega
      · exact (Nat.le_div_iff_mul_le hp).2 (by omega)
    rw [Nat.log2_lt (Nat.pos_iff_ne_zero.1 h0)]
    have hs : (a ^^^ b) >>> a.log2 = 0 := by
      rw [xorFoldR_shiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, key a ha, h,
        key b hb]
      rfl
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at hs
    rcases hs with hs | hs
    · exact absurd hs (Nat.pos_iff_ne_zero.1 (Nat.two_pow_pos _))
    · exact hs

@[expose] def hypTable (T : Array Nat) (φ : Nat) : Bool :=
  par128 (φ &&& 1) == 1 && (List.range 77).all fun q =>
    T[q + 1]?.getD 0 != 0 && (T[q + 1]?.getD 0).log2 == q + 1 &&
      par128 (φ &&& T[q + 1]?.getD 0) == 0

theorem insertVec_hyp {T : Array Nat} {φ : Nat} (hT : hypTable T φ = true) :
    ∀ m v, m ≤ 78 → (v = 0 ∨ v.log2 + 1 ≤ m) → par128 (φ &&& v) = 0 →
      insertVec T (m + 1) v = some T
  | m, v, hm, hv, hp => by
    have hT2 := hT
    simp only [hypTable, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      bne_iff_ne, ne_eq] at hT2
    obtain ⟨hφ, hT2⟩ := hT2
    rw [insertVec]
    by_cases h0 : v = 0
    · simp only [h0, ↓reduceIte]
    simp only [h0, ↓reduceIte]
    have hl := hv.resolve_left h0
    rcases Nat.eq_zero_or_pos v.log2 with hz | hz
    · have hv1 : v = 1 := by
        have := (Nat.log2_lt (k := 1) h0).1 (by omega)
        omega
      rw [hv1, hφ] at hp
      exact absurd hp (by decide)
    obtain ⟨⟨htz, htl⟩, htp⟩ := hT2 (v.log2 - 1) (by omega)
    rw [Nat.sub_add_cancel hz] at htz htl htp
    simp only [htz, ↓reduceIte]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine insertVec_hyp hT m' _ (by omega) ?_ ?_
    · rcases xor_log2_lt_of_log2_eq h0 htz htl.symm with h | h
      · exact Or.inl h
      · right
        omega
    · rw [Nat.and_xor_distrib_left, par128_xor, hp, htp]
      rfl

theorem elimList_hyp {T : Array Nat} {φ : Nat} (hT : hypTable T φ = true) :
    ∀ vs : List Nat, (vs.all fun v => decide (v < 2 ^ 78) && par128 (φ &&& v) == 0) = true →
      elimList 78 T vs = some T
  | [], _ => rfl
  | v :: vs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨hv, hp⟩, h⟩ := h
    have hi : insertVec T (78 + 1) v = some T := by
      refine insertVec_hyp hT 78 v (Nat.le_refl _) ?_ hp
      by_cases h0 : v = 0
      · exact Or.inl h0
      · exact Or.inr (Nat.succ_le_of_lt ((Nat.log2_lt h0).2 hv))
    rw [elimList, hi]
    exact elimList_hyp hT vs h

theorem elimList_append (d : Nat) :
    ∀ (T : Array Nat) (us vs : List Nat),
      elimList d T (us ++ vs) = (elimList d T us).bind fun T' => elimList d T' vs
  | T, [], vs => rfl
  | T, u :: us, vs => by
    rw [List.cons_append, elimList, elimList]
    cases insertVec T (d + 1) u with
    | none => rfl
    | some T' => exact elimList_append d T' us vs

@[expose] noncomputable def pk128 (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun r _ acc => r ||| (acc <<< 128)) L

@[expose] noncomputable def msk128 (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc ||| (1 <<< (128 * i))) n

@[expose] noncomputable def cc127 (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => acc + (1 <<< (127 * i))) n

@[expose] noncomputable def trPk (R T : List Nat) : Bool :=
  T.length == 78 && allIdx (fun _ r => Nat.blt r (2 ^ 128)) R 0 &&
    allIdx (fun j t => Nat.blt t (2 ^ 78) &&
      ((pk128 R >>> j) &&& msk128 78) == ((t * cc127 78) &&& msk128 78)) T 0

theorem testBit_pk128 : ∀ (L : List Nat), (∀ r ∈ L, r < 2 ^ 128) → ∀ i j, j < 128 →
    (pk128 L).testBit (128 * i + j) = (L[i]?.getD 0).testBit j
  | [], _, i, j, _ => by simp [pk128]
  | r :: L, h, i, j, hj => by
    change (r ||| (pk128 L <<< 128)).testBit _ = _
    have hr := h r List.mem_cons_self
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [hj]
    | succ i =>
      have e : 128 * (i + 1) + j - 128 = 128 * i + j := by omega
      rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega)
        (by omega))), e, testBit_pk128 L (fun r hr => h r (List.mem_cons_of_mem _ hr)) i j hj]
      have h128 : 128 * (i + 1) + j ≥ 128 := by omega
      simp [h128]

theorem testBit_msk128 : ∀ n i, i < n → (msk128 n).testBit (128 * i) = true
  | 0, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    change (msk128 n ||| 1 <<< (128 * n)).testBit _ = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [testBit_msk128 n i h, Bool.true_or]
    · simp

theorem mul_cc127 (t : Nat) (ht : t < 2 ^ 127) : ∀ n, n ≤ 127 →
    t * cc127 n < 2 ^ (127 * n) ∧ ∀ i < n, (t * cc127 n).testBit (128 * i) = t.testBit i
  | 0, _ => by simp [cc127]
  | n + 1, hn => by
    obtain ⟨hlt, hb⟩ := mul_cc127 t ht n (by omega)
    have he : t * cc127 (n + 1) = t <<< (127 * n) + t * cc127 n := by
      change t * (cc127 n + 1 <<< (127 * n)) = _
      rw [Nat.mul_add, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.add_comm]
    refine ⟨?_, ?_⟩
    · have hm : t * 2 ^ (127 * n) ≤ (2 ^ 127 - 1) * 2 ^ (127 * n) :=
        Nat.mul_le_mul_right _ (by omega)
      have hp : 2 ^ (127 * (n + 1)) = 2 ^ 127 * 2 ^ (127 * n) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      rw [he, Nat.shiftLeft_eq, hp]
      rw [Nat.sub_mul, Nat.one_mul] at hm
      have h1 : 2 ^ (127 * n) ≤ 2 ^ 127 * 2 ^ (127 * n) :=
        Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      omega
    · intro i hi
      rw [he, Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_shiftLeft]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have : ¬ 127 * n ≤ 128 * i := by omega
        simp [this, hb i hi]
      · rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega)
          (by omega)))]
        have e : 128 * i - 127 * i = i := by omega
        have e' : 127 * i ≤ 128 * i := by omega
        simp [e, e']

theorem ofBits_testBit_fold (f : Nat → Bool) (i : Nat) (L : List Nat) (acc : Nat) :
    (L.foldl (fun acc j => if f j then acc ||| (1 <<< j) else acc) acc).testBit i =
      (acc.testBit i || (decide (i ∈ L) && f i)) := by
  induction L generalizing acc with
  | nil => simp
  | cons a L ih =>
    rw [List.foldl_cons, ih]
    by_cases hi : a = i
    · subst hi
      by_cases h : f a = true <;> simp [h, Nat.testBit_or, Nat.one_shiftLeft]
    · by_cases h : f a = true <;>
        simp [h, hi, Ne.symm hi, Nat.testBit_or, Nat.one_shiftLeft]

theorem transposeRows_of_trPk {R : Array Nat} {T : List Nat} (h : trPk R.toList T = true) :
    transposeRows 78 R = T.toArray := by
  simp only [trPk, Bool.and_eq_true, beq_iff_eq, allIdx_iff, Nat.blt_eq, Nat.zero_add] at h
  obtain ⟨⟨hlen, hR⟩, hT⟩ := h
  have hR' : ∀ r ∈ R.toList, r < 2 ^ 128 := fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hr
    exact hR k hk
  apply Array.ext
  · simp [transposeRows, hlen]
  · intro j hj1 hj2
    simp only [transposeRows, Array.getElem_ofFn, List.getElem_toArray]
    have hj : j < T.length := by simpa using hj2
    obtain ⟨htlt, heq⟩ := hT j hj
    apply Nat.eq_of_testBit_eq
    intro i
    rw [ofBits, ofBits_testBit_fold, Nat.zero_testBit, Bool.false_or]
    simp only [List.mem_range]
    by_cases hi : i < 78
    · have hb := congrArg (fun x => x.testBit (128 * i)) heq
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_msk128 78 i hi,
        Bool.and_true] at hb
      rw [(mul_cc127 _ (by omega) 78 (by omega)).2 i hi, Nat.add_comm,
        testBit_pk128 R.toList hR' i j (by omega), Array.getElem?_toList] at hb
      simp [hi, hb]
    · rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le htlt (Nat.pow_le_pow_right (by omega)
        (by omega)))]
      simp [hi]

@[expose] noncomputable def gt128 (P p : Nat) : Nat := (P >>> (128 * p)) &&& (2 ^ 128 - 1)

@[expose] noncomputable def st128 (P p v : Nat) : Nat := P ^^^ ((gt128 P p ^^^ v) <<< (128 * p))

@[expose] noncomputable def unpk128 (P : Nat) : Array Nat := Array.ofFn (n := 78) fun i => gt128 P i.val

@[expose] noncomputable def insPk (P : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, v =>
    if v = 0 then some P
    else if Nat.log2 v < 78 then
      if gt128 P (Nat.log2 v) = 0 then some (st128 P (Nat.log2 v) v)
      else insPk P fuel (v ^^^ gt128 P (Nat.log2 v))
    else some P

@[expose] noncomputable def elimPk : Nat → List Nat → Option Nat
  | P, [] => some P
  | P, v :: vs =>
    match insPk P (78 + 1) v with
    | none => none
    | some P' => elimPk P' vs

theorem testBit_gt128 (P p b : Nat) :
    (gt128 P p).testBit b = (decide (b < 128) && P.testBit (128 * p + b)) := by
  simp only [gt128, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
    Bool.and_comm]

theorem gt128_st128 {v : Nat} (hv : v < 2 ^ 128) (P p q : Nat) :
    gt128 (st128 P p v) q = if q = p then v else gt128 P q := by
  apply Nat.eq_of_testBit_eq
  intro b
  have hvb : ∀ c, 128 ≤ c → v.testBit c = false := fun c hc =>
    Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega) hc))
  by_cases hq : q = p
  · subst hq
    simp only [testBit_gt128, st128, Nat.testBit_xor, Nat.testBit_shiftLeft, ↓reduceIte]
    by_cases hb : b < 128
    · have e : 128 * q + b - 128 * q = b := by omega
      simp only [hb, e, decide_true, Bool.true_and, Nat.le_add_right]
      cases P.testBit (128 * q + b) <;> cases v.testBit b <;> rfl
    · simp [hb, hvb b (by omega)]
  · simp only [testBit_gt128, st128, Nat.testBit_xor, Nat.testBit_shiftLeft, hq, ↓reduceIte]
    by_cases hb : b < 128
    · rcases Nat.lt_or_ge q p with h | h
      · have : ¬ 128 * p ≤ 128 * q + b := by omega
        simp [this]
      · have e : 128 ≤ 128 * q + b - 128 * p := by omega
        simp [hb, Nat.not_lt.2 e, hvb _ e]
    · simp [hb]

theorem getD_unpk128 (P p : Nat) :
    (unpk128 P)[p]?.getD 0 = if p < 78 then gt128 P p else 0 := by
  by_cases h : p < 78 <;> simp [unpk128, h]

theorem set_unpk128 {P p v : Nat} (hv : v < 2 ^ 128) :
    (unpk128 P).setIfInBounds p v = unpk128 (st128 P p v) := by
  apply Array.ext
  · simp [unpk128]
  · intro j hj1 hj2
    have hj : j < (unpk128 P).size := by simpa [unpk128] using hj2
    rw [Array.getElem_setIfInBounds hj]
    simp only [unpk128, Array.getElem_ofFn, gt128_st128 hv]
    by_cases h : p = j
    · simp [h]
    · simp [h, Ne.symm h]

theorem set_unpk128_ge {P p : Nat} (hp : ¬ p < 78) (v : Nat) :
    (unpk128 P).setIfInBounds p v = unpk128 P := by
  apply Array.ext
  · simp [unpk128]
  · intro j hj1 hj2
    have hj : j < 78 := by simpa [unpk128] using hj2
    have h : p ≠ j := by omega
    rw [Array.getElem_setIfInBounds hj2]
    simp only [h, ↓reduceIte]

theorem insertVec_unpk128 : ∀ (fuel P v : Nat),
    insertVec (unpk128 P) fuel v = (insPk P fuel v).map unpk128
  | 0, _, _ => rfl
  | fuel + 1, P, v => by
    rw [insertVec, insPk]
    by_cases h0 : v = 0
    · simp [h0]
    simp only [h0, ↓reduceIte, getD_unpk128]
    by_cases hl : Nat.log2 v < 78
    · have hv : v < 2 ^ 128 :=
        Nat.lt_of_lt_of_le ((Nat.log2_lt h0).1 hl) (Nat.pow_le_pow_right (by omega) (by omega))
      simp only [hl, ↓reduceIte]
      by_cases ht : gt128 P (Nat.log2 v) = 0
      · simp [ht, set_unpk128 hv]
      · simp only [ht, ↓reduceIte]
        exact insertVec_unpk128 fuel P _
    · simp [hl, set_unpk128_ge hl]

theorem elimList_unpk128 : ∀ (vs : List Nat) (P : Nat),
    elimList 78 (unpk128 P) vs = (elimPk P vs).map unpk128
  | [], _ => rfl
  | v :: vs, P => by
    rw [elimList, elimPk, insertVec_unpk128]
    cases insPk P (78 + 1) v with
    | none => rfl
    | some P' => exact elimList_unpk128 vs P'

theorem replicate_unpk128 : Array.replicate 78 0 = unpk128 0 := by
  apply Array.ext
  · simp [unpk128]
  · intro j hj1 hj2
    simp [unpk128, gt128]

theorem unpk128_pk128 {L : List Nat} (hlen : L.length = 78) (hL : ∀ r ∈ L, r < 2 ^ 128) :
    unpk128 (pk128 L) = L.toArray := by
  apply Array.ext
  · simp [unpk128, hlen]
  · intro j hj1 hj2
    simp only [unpk128, Array.getElem_ofFn, List.getElem_toArray]
    apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_gt128]
    have hj : j < L.length := by simpa using hj2
    by_cases hb : b < 128
    · rw [testBit_pk128 L hL j b hb]
      simp [hb, hj]
    · rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hL _ (List.getElem_mem hj))
        (Nat.pow_le_pow_right (by omega) (by omega)))]
      simp [hb]

@[expose] def fTrs : List (List Nat) :=
  [fTr0, fTr1, fTr2, fTr3, fTr4, fTr5, fTr6, fTr7, fTr8, fTr9, fTr10, fTr11]

@[expose] def subOneT : List Nat :=
  (List.range 12).flatMap fun k => (List.range 78).map fun i => (fTrs[k]!).toArray[i]! ^^^ (1 <<< i)

theorem basisPt_lt : ∀ i < 78, basisPt i < 3510 := by decide +kernel

theorem kShape : fShapeCheck = true := by decide +kernel

theorem kLen : GramLit.rowCoords.length = 3510 := by decide +kernel

@[expose] noncomputable def lcPack : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ acc => Nat.lor c (Nat.shiftLeft acc 78))
    GramLit.rowCoords

theorem kPack : packW 78 lcPack GramLit.rowCoords 0 = true := by decide +kernel

theorem labelCoord_pack {y : Nat} (hy : y < 3510) : labelCoord y = fget lcPack y 78 :=
  packW_get kPack (by rw [kLen]; exact hy)

theorem kColPack : ((List.range 12).all fun k => (List.range 78).all fun i =>
    Nat.blt (candF k (basisPt i)) 3510 &&
      fCol k i == fget lcPack (candF k (basisPt i)) 78) = true := by
  decide +kernel

theorem kCol : ((List.range 12).all fun k => (List.range 78).all fun i =>
    fCol k i == labelCoord (candF k (basisPt i))) = true := by
  have h := kColPack
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h ⊢
  intro k hk i hi
  obtain ⟨hb, he⟩ := h k hk i hi
  rw [labelCoord_pack (by simpa using hb)]
  exact he

theorem kFix : fFixCheck = true := by decide +kernel

theorem kTrPk : ∀ k < 12, trPk (fColArr[k]!).toList (fTrs[k]!) = true := by decide +kernel

theorem kTr : ∀ k < 12, (transposeRows 78 (fColArr[k]!)).toList = fTrs[k]! := fun k hk => by
  rw [transposeRows_of_trPk (kTrPk k hk), List.toList_toArray]

@[expose] noncomputable def xorDiag (T : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun r _ ih i => (r ^^^ (1 <<< i)) :: ih (i + 1)) T

@[expose] noncomputable def subOneW : List Nat :=
  (List.range 12).flatMap fun k => xorDiag (fTrs[k]!) 0

theorem xorDiag_eq : ∀ (T : List Nat) (i : Nat),
    xorDiag T i = (List.range T.length).map fun q => T.toArray[q]! ^^^ (1 <<< (i + q))
  | [], _ => rfl
  | r :: T, i => by
    change (r ^^^ (1 <<< i)) :: xorDiag T (i + 1) = _
    rw [xorDiag_eq T (i + 1), List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    congr 1
    simp
    intro a _
    rw [Nat.add_assoc, Nat.add_comm 1 a]

theorem subOneT_eq : subOneT = subOneW := by
  rw [subOneT, subOneW]
  apply List.flatMap_congr
  intro k hk
  have hl : (fTrs[k]!).length = 78 := by
    rw [← kTr k (List.mem_range.1 hk), Array.length_toList, transposeRows, Array.size_ofFn]
  rw [xorDiag_eq, hl]
  simp

theorem kElimPk : (elimPk 0 (subOneW.take 168) == some (pk128 fElim)) = true := by
  decide +kernel

theorem kElimLen :
    (fElim.length == 78 && allIdx (fun _ r => Nat.blt r (2 ^ 128)) fElim 0) = true := by
  decide +kernel

theorem kElimPre :
    (elimList 78 (Array.replicate 78 0) (subOneT.take 168) == some fElim.toArray) = true := by
  have h := kElimLen
  simp only [Bool.and_eq_true, beq_iff_eq, allIdx_iff, Nat.blt_eq] at h
  have hL : ∀ r ∈ fElim, r < 2 ^ 128 := fun r hr => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hr
    exact h.2 k hk
  rw [subOneT_eq, replicate_unpk128, elimList_unpk128, beq_iff_eq.1 kElimPk, Option.map_some,
    unpk128_pk128 h.1 hL]
  exact beq_self_eq_true _

theorem kElimHyp : hypTable fElim.toArray 949 = true := by decide +kernel

theorem kElimPost :
    ((subOneT.drop 168).all fun v => decide (v < 2 ^ 78) && par128 (949 &&& v) == 0) = true := by
  rw [subOneT_eq]
  decide +kernel

theorem elim_eq : elimTable 78 subOneT = some fElim.toArray := by
  rw [elimTable, ← List.take_append_drop 168 subOneT, elimList_append, beq_iff_eq.1 kElimPre,
    Option.bind_some, elimList_hyp kElimHyp _ kElimPost]

theorem kElim : (elimTable 78 subOneT == some fElim.toArray) = true := beq_iff_eq.2 elim_eq

theorem kBelow : allBelow 78 subOneT = true := by
  rw [subOneT_eq]
  decide +kernel

theorem kRankT : rankOpt 78 77 (some fElim.toArray) = true := by decide +kernel

theorem kFreeT : ((List.range 78).all fun p => (fElim.toArray[p]! == 0) == [0].contains p) = true := by
  decide +kernel

theorem kRank : spanRankIs 78 subOneT 77 = true := by
  rw [spanRankIs, elim_eq, kBelow, kRankT]
  rfl

theorem kFree : freeIs 78 subOneT [0] = true := by
  rw [freeIs, elim_eq, kBelow]
  exact kFreeT

theorem kClique : spanRankIs 78 ((List.range 22).map labelCoord) 11 = true := by decide +kernel

theorem kCoordNe : allIdx (fun _ c => c != 949 && decide (c < 2 ^ 78)) GramLit.rowCoords 0 = true := by
  decide +kernel

theorem kMask : maskSum = 949 := by decide +kernel

theorem fColCheck_true : fColCheck = true := by
  rw [← kCol]
  unfold fColCheck
  apply all_range_congr
  intro k hk
  apply all_range_congr
  intro i hi
  rw [cand_get (by omega) (basisPt_lt i hi)]

theorem subOneRows_eq : subOneRows (List.range 12) = subOneT := by
  rw [subOneRows, subOneT, List.flatMap_def, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun k hk => ?_)
  have h := kTr k (List.mem_range.1 hk)
  have h' : transposeRows 78 (fColArr[k]!) = (fTrs[k]!).toArray := by
    rw [← h, Array.toArray_toList]
  rw [h']

theorem coordNeCheck_true : coordNeCheck = true := by
  unfold coordNeCheck
  rw [← kLen]
  exact (range_all_eq_allIdx (fun _ c => c != 949 && decide (c < 2 ^ 78)) GramLit.rowCoords).trans
    kCoordNe

theorem facts : (fShapeCheck = true) ∧ (fColCheck = true) ∧ (fFixCheck = true)
    ∧ (spanRankIs 78 (subOneRows (List.range 12)) 77 = true)
    ∧ (freeIs 78 (subOneRows (List.range 12)) [0] = true)
    ∧ (spanRankIs 78 ((List.range 22).map labelCoord) 11 = true)
    ∧ (coordNeCheck = true) ∧ (maskSum = 949) := by
  rw [subOneRows_eq]
  exact ⟨kShape, fColCheck_true, kFix, kRank, kFree, kClique, coordNeCheck_true, kMask⟩

end CertificateChecks.KernelMonB.Fischer3066

end
