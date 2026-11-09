module

public import Certificates.Kernel.OmegaEight.SB3871NK
public import Certificates.Kernel.OmegaEight.SB3871MaskData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

set_option maxHeartbeats 0 in
theorem nStep0 : ∀ s < (nBlocks 0).length, nStepOK 0 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 0).length = 1)] at hs
  refine nStepOK_of_B (by norm_num) ?_
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep1 : ∀ s < (nBlocks 1).length, nStepOK 1 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 1).length = 1)] at hs
  refine nStepOK_of_B (by norm_num) ?_
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep2 : ∀ s < (nBlocks 2).length, nStepOK 2 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 2).length = 1)] at hs
  refine nStepOK_of_B (by norm_num) ?_
  interval_cases s
  decide +kernel

@[expose] noncomputable def n1Idx (v : ℕ) : ℕ := bif Nat.blt v 36 then Nat.sub v 8 else Nat.sub v 24

@[expose] noncomputable def n1MaskRow (e : ℕ) : ℕ :=
  vL.vL3.foldr (fun v acc => Nat.lor (2 ^ (32 * Nat.xor (MK e v) v + n1Idx v)) acc) 0

theorem n1Mask_ok : ((List.range 128).all fun e => Nat.beq (n1Mask e) (n1MaskRow e)) = true := by
  decide +kernel

theorem n1Idx_lt : ∀ v ∈ vL.vL3, n1Idx v < 32 := by decide +kernel

@[expose] noncomputable def n1MaskK (e b : ℕ) : ℕ :=
  bif Nat.blt e 128 then Nat.land (Nat.shiftRight (n1Mask e) (32 * b)) 4294967295 else 4294967295

@[expose] noncomputable def n1OrM (b : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun e _ ih => Nat.lor (n1MaskK e b) ih) l

theorem n1_testBit_foldr_pow {L : List ℕ} {g : ℕ → ℕ} {v : ℕ} (hv : v ∈ L) :
    Nat.testBit (L.foldr (fun v acc => Nat.lor (2 ^ g v) acc) 0) (g v) = true := by
  induction L with
  | nil => cases hv
  | cons x t ih =>
    rw [List.foldr_cons]
    change Nat.testBit (2 ^ g x ||| _) _ = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.1 hv with h | h
    · subst h
      simp
    · rw [ih h, Bool.or_true]

theorem n1MaskK_bit {e b k : ℕ} (hk : k < 32)
    (h : e < 128 → Nat.testBit (n1Mask e) (32 * b + k) = true) : Nat.testBit (n1MaskK e b) k = true := by
  have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  unfold n1MaskK
  cases he : Nat.blt e 128
  · rw [Bool.cond_false, h32, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hk
  · rw [Bool.cond_true, h32]
    change Nat.testBit ((n1Mask e >>> (32 * b)) &&& (2 ^ 32 - 1)) k = true
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one,
      h (Nat.blt_eq.mp he)]
    simp [hk]

theorem n1OrM_bit {b k e : ℕ} {l : List ℕ} (he : e ∈ l) (h : Nat.testBit (n1MaskK e b) k = true) :
    Nat.testBit (n1OrM b l) k = true := by
  induction l with
  | nil => cases he
  | cons x t ih =>
    change Nat.testBit (n1MaskK x b ||| n1OrM b t) k = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.1 he with h' | h'
    · subst h'
      rw [h, Bool.true_or]
    · rw [ih h', Bool.or_true]

theorem n1OrM_of_filter {l : List ℕ} {b c v : ℕ} (hc : c = v) (hv : v ∈ vL.vL3)
    (h : (!(l.filter fun e => MK e v == Nat.xor b c).isEmpty) = true) :
    Nat.testBit (n1OrM b l) (n1Idx v) = true := by
  subst hc
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil (l.filter fun e => MK e c == Nat.xor b c)
    fun h0 => by
      rw [h0] at h
      exact absurd h (by decide)
  rw [List.mem_filter, beq_iff_eq] at he
  have hb : b = Nat.xor (MK e c) c := by
    rw [he.2]
    change b = (b ^^^ c) ^^^ c
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  refine n1OrM_bit he.1 (n1MaskK_bit (n1Idx_lt c hv) fun hlt => ?_)
  have hrow := Nat.eq_of_beq_eq_true (List.all_eq_true.1 n1Mask_ok e (List.mem_range.2 hlt))
  rw [hrow, hb]
  exact n1_testBit_foldr_pow (g := fun v => 32 * Nat.xor (MK e v) v + n1Idx v) hv

theorem n1_testBit_land {a b k : ℕ} (ha : Nat.testBit a k = true) (hb : Nat.testBit b k = true) :
    Nat.testBit (Nat.land a b) k = true := by
  change Nat.testBit (a &&& b) k = true
  rw [Nat.testBit_and, ha, hb, Bool.and_self]

theorem n1_ite_guard {α : Type} {T C : Bool} {x : Option α} (h : C = true → T = true) :
    (if C = true then x else none) = (bif T then (if C = true then x else none) else none) := by
  cases T <;> cases C
  · rfl
  · exact absurd (h rfl) (by decide)
  · rfl
  · rfl

theorem n1_testBit_foldr_any {L : List ℕ} {g : ℕ → ℕ} {n : ℕ} :
    Nat.testBit (L.foldr (fun v acc => Nat.lor (2 ^ g v) acc) 0) n =
      L.any fun v => decide (g v = n) := by
  induction L with
  | nil => exact Nat.zero_testBit n
  | cons x t ih =>
    rw [List.foldr_cons, List.any_cons, ← ih]
    change Nat.testBit (2 ^ g x ||| _) _ = _
    rw [Nat.testBit_or, Nat.testBit_two_pow]

theorem n1Idx_inj : ∀ v ∈ vL.vL3, ∀ w ∈ vL.vL3, n1Idx v = n1Idx w → v = w := by decide +kernel

theorem n1_xor_xor (a b : ℕ) : Nat.xor (Nat.xor a b) b = a := by
  change (a ^^^ b) ^^^ b = a
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem n1MaskK_exact {e b v : ℕ} (he : e < 128) (hv : v ∈ vL.vL3) :
    Nat.testBit (n1MaskK e b) (n1Idx v) = (MK e v == Nat.xor b v) := by
  have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  have hk := n1Idx_lt v hv
  have hrow := Nat.eq_of_beq_eq_true (List.all_eq_true.1 n1Mask_ok e (List.mem_range.2 he))
  unfold n1MaskK
  rw [Nat.blt_eq.mpr he, Bool.cond_true, h32]
  change Nat.testBit ((n1Mask e >>> (32 * b)) &&& (2 ^ 32 - 1)) (n1Idx v) = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one, decide_eq_true hk,
    Bool.and_true, hrow, n1MaskRow, n1_testBit_foldr_any]
  refine Bool.eq_iff_iff.2 ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨w, hw, h⟩ := List.any_eq_true.1 h
    have hw32 := n1Idx_lt w hw
    have h' := of_decide_eq_true h
    have hx : Nat.xor (MK e w) w = b := by omega
    rw [n1Idx_inj w hw v hv (by omega)] at hx
    rw [beq_iff_eq, ← hx, n1_xor_xor]
  · refine List.any_eq_true.2 ⟨v, hv, decide_eq_true ?_⟩
    rw [beq_iff_eq.1 h, n1_xor_xor]

theorem n1MaskK_high {e b i : ℕ} (hi : 32 ≤ i) : Nat.testBit (n1MaskK e b) i = false := by
  have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  have hi' : decide (i < 32) = false := decide_eq_false (by omega)
  unfold n1MaskK
  cases Nat.blt e 128
  · rw [Bool.cond_false, h32, Nat.testBit_two_pow_sub_one, hi']
  · rw [Bool.cond_true, h32]
    change Nat.testBit ((n1Mask e >>> (32 * b)) &&& (2 ^ 32 - 1)) i = false
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, hi', Bool.and_false]

theorem n1_low_pack {x y i : ℕ} (hi : i < 32) :
    Nat.testBit (Nat.lor x (Nat.shiftLeft y 32)) i = Nat.testBit x i := by
  change Nat.testBit (x ||| y <<< 32) i = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, decide_eq_false (by omega : ¬ i ≥ 32),
    Bool.false_and, Bool.or_false]

theorem n1_shr_pack {x y : ℕ} (hx : ∀ i, 32 ≤ i → Nat.testBit x i = false) :
    Nat.shiftRight (Nat.lor x (Nat.shiftLeft y 32)) 32 = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  change Nat.testBit ((x ||| y <<< 32) >>> 32) i = _
  rw [Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, hx _ (by omega),
    decide_eq_true (by omega : 32 + i ≥ 32), Nat.add_sub_cancel_left, Bool.false_or, Bool.true_and]

theorem n1_land_pack {x y : ℕ} (hx : ∀ i, 32 ≤ i → Nat.testBit x i = false) :
    Nat.land (Nat.lor x (Nat.shiftLeft y 32)) 4294967295 = x := by
  have h32 : (4294967295 : ℕ) = 2 ^ 32 - 1 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro i
  rw [h32]
  change Nat.testBit ((x ||| y <<< 32) &&& (2 ^ 32 - 1)) i = _
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 32
  · rw [decide_eq_true hi, Bool.and_true]
    exact n1_low_pack hi
  · rw [decide_eq_false hi, Bool.and_false, hx i (by omega)]

@[expose] noncomputable def n1Pack (b : ℕ) (l : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun e _ ih => Nat.lor (n1MaskK e b) (Nat.shiftLeft ih 32)) l

@[expose] noncomputable def n1OrP (l : List ℕ) (p : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun _ _ ih p => Nat.lor (Nat.land p 4294967295) (ih (Nat.shiftRight p 32))) l p

@[expose] noncomputable def n1Bit (m k : ℕ) : Bool := Nat.beq (Nat.land 1 (Nat.shiftRight m k)) 1

theorem n1Bit_eq (m k : ℕ) : n1Bit m k = Nat.testBit m k := by
  have hy : Nat.land 1 (Nat.shiftRight m k) < 2 := by
    change 1 &&& (m >>> k) < 2
    rw [Nat.one_and_eq_mod_two]
    exact Nat.mod_lt _ (by norm_num)
  unfold n1Bit Nat.testBit
  change Nat.beq (Nat.land 1 (Nat.shiftRight m k)) 1 = (Nat.land 1 (Nat.shiftRight m k) != 0)
  generalize Nat.land 1 (Nat.shiftRight m k) = y at hy ⊢
  interval_cases y <;> rfl

@[expose] noncomputable def n1Sel (b v k : ℕ) (l : List ℕ) (p : ℕ) : List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun e _ ih p => bif (bif Nat.blt e 128 then n1Bit p k else MK e v == Nat.xor b v)
      then e :: ih (Nat.shiftRight p 32) else ih (Nat.shiftRight p 32)) l p

theorem n1OrP_pack (b : ℕ) (l : List ℕ) : n1OrP l (n1Pack b l) = n1OrM b l := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    change Nat.lor (Nat.land (n1Pack b (e :: t)) 4294967295)
      (n1OrP t (Nat.shiftRight (n1Pack b (e :: t)) 32)) = Nat.lor (n1MaskK e b) (n1OrM b t)
    have hx : ∀ i, 32 ≤ i → Nat.testBit (n1MaskK e b) i = false := fun _ hi => n1MaskK_high hi
    have hpk : n1Pack b (e :: t) = Nat.lor (n1MaskK e b) (Nat.shiftLeft (n1Pack b t) 32) := rfl
    rw [hpk, n1_land_pack hx, n1_shr_pack hx, ih]

theorem n1Sel_eq {b v : ℕ} (hv : v ∈ vL.vL3) (l : List ℕ) :
    n1Sel b v (n1Idx v) l (n1Pack b l) = l.filter fun e => MK e v == Nat.xor b v := by
  induction l with
  | nil => rfl
  | cons e t ih =>
    have hx : ∀ i, 32 ≤ i → Nat.testBit (n1MaskK e b) i = false := fun _ hi => n1MaskK_high hi
    have ht : (bif Nat.blt e 128 then n1Bit (n1Pack b (e :: t)) (n1Idx v)
        else MK e v == Nat.xor b v) = (MK e v == Nat.xor b v) := by
      cases he : Nat.blt e 128
      · rfl
      · rw [Bool.cond_true, n1Bit_eq]
        change Nat.testBit (Nat.lor (n1MaskK e b) (Nat.shiftLeft (n1Pack b t) 32)) (n1Idx v) = _
        rw [n1_low_pack (n1Idx_lt v hv), n1MaskK_exact (Nat.blt_eq.mp he) hv]
    have hp : Nat.shiftRight (n1Pack b (e :: t)) 32 = n1Pack b t := n1_shr_pack hx
    change (bif (bif Nat.blt e 128 then n1Bit (n1Pack b (e :: t)) (n1Idx v)
        else MK e v == Nat.xor b v)
      then e :: n1Sel b v (n1Idx v) t (Nat.shiftRight (n1Pack b (e :: t)) 32)
      else n1Sel b v (n1Idx v) t (Nat.shiftRight (n1Pack b (e :: t)) 32)) = _
    rw [ht, hp, ih, List.filter_cons]
    cases MK e v == Nat.xor b v <;> rfl

@[expose] noncomputable def n1FM {β : Type} (f : ℕ → Option β) (l : List ℕ) : List β :=
  List.rec (motive := fun _ => List β) []
    (fun v _ ih => Option.rec (motive := fun _ => List β) ih (fun y => y :: ih) (f v)) l

theorem n1FM_eq {β : Type} (f : ℕ → Option β) (l : List ℕ) : n1FM f l = l.filterMap f := by
  induction l with
  | nil => rfl
  | cons v t ih =>
    change Option.rec (motive := fun _ => List β) (n1FM f t) (fun y => y :: n1FM f t) (f v) = _
    rw [List.filterMap_cons, ih]
    cases f v <;> rfl

@[expose] noncomputable def n1Run {β : Type} (m : ℕ) (vs : List ℕ) (h : ℕ → Option β) : List β :=
  bif Nat.beq m 0 then [] else n1FM (fun v => bif n1Bit m (n1Idx v) then h v else none) vs

theorem n1Run_eq {β : Type} (m : ℕ) (vs : List ℕ) (h : ℕ → Option β) :
    n1Run m vs h = vs.filterMap fun v => bif n1Bit m (n1Idx v) then h v else none := by
  unfold n1Run
  rw [n1FM_eq]
  cases hm : Nat.beq m 0
  · rfl
  · have h0 := Nat.eq_of_beq_eq_true hm
    subst h0
    refine (List.filterMap_eq_nil_iff.2 fun v _ => ?_).symm
    rw [n1Bit_eq, Nat.zero_testBit]
    rfl

@[expose] noncomputable def nStepM (cb : ℕ → ℕ → ℕ) (vs : List ℕ) (i : ℕ)
    (st : List ℕ × List (List ℕ)) : List (List ℕ × List (List ℕ)) :=
  strictL (xorK i st.1 (cb 0 i)) fun b0 => strictL (xorK i st.1 (cb 1 i)) fun b1 =>
  strictL (xorK i st.1 (cb 2 i)) fun b2 => strictL (xorK i st.1 (cb 3 i)) fun b3 =>
  strictL (xorK i st.1 (cb 4 i)) fun b4 => strictL (xorK i st.1 (cb 5 i)) fun b5 =>
  strictL (xorK i st.1 (cb 6 i)) fun b6 =>
  strictL (n1Pack b0 (st.2.getD 0 [])) fun p0 => strictL (n1Pack b1 (st.2.getD 1 [])) fun p1 =>
  strictL (n1Pack b2 (st.2.getD 2 [])) fun p2 => strictL (n1Pack b3 (st.2.getD 3 [])) fun p3 =>
  strictL (n1Pack b4 (st.2.getD 4 [])) fun p4 => strictL (n1Pack b5 (st.2.getD 5 [])) fun p5 =>
  strictL (n1Pack b6 (st.2.getD 6 [])) fun p6 =>
  strictL (Nat.land (n1OrP (st.2.getD 0 []) p0) (Nat.land (n1OrP (st.2.getD 1 []) p1)
    (Nat.land (n1OrP (st.2.getD 2 []) p2) (Nat.land (n1OrP (st.2.getD 3 []) p3)
    (Nat.land (n1OrP (st.2.getD 4 []) p4) (Nat.land (n1OrP (st.2.getD 5 []) p5)
    (n1OrP (st.2.getD 6 []) p6))))))) fun m =>
  n1Run m vs fun v =>
    let Vs := st.1 ++ [v]
    let k := n1Idx v
    let newc := [n1Sel b0 v k (st.2.getD 0 []) p0, n1Sel b1 v k (st.2.getD 1 []) p1,
      n1Sel b2 v k (st.2.getD 2 []) p2, n1Sel b3 v k (st.2.getD 3 []) p3,
      n1Sel b4 v k (st.2.getD 4 []) p4, n1Sel b5 v k (st.2.getD 5 []) p5,
      n1Sel b6 v k (st.2.getD 6 []) p6]
    if newc.all (fun l => !l.isEmpty) then some (Vs, newc) else none

theorem nStepB_eq_nStepM {cb : ℕ → ℕ → ℕ} {vs : List ℕ} {i : ℕ}
    (hvs : ∀ v ∈ vs, v ∈ vL.vL3) (hcb : ∀ j < 7, ∀ v, bitV (cb j i) i v = v)
    (st : List ℕ × List (List ℕ)) : nStepB MK cb vs i st = nStepM cb vs i st := by
  unfold nStepB nStepM
  simp only [strictL_eq, n1OrP_pack, n1Run_eq]
  refine List.filterMap_congr fun v hv => ?_
  have hv' := hvs v hv
  have h7 : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  simp only [h7, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ,
    hcb 0 (by norm_num) v, hcb 1 (by norm_num) v, hcb 2 (by norm_num) v, hcb 3 (by norm_num) v,
    hcb 4 (by norm_num) v, hcb 5 (by norm_num) v, hcb 6 (by norm_num) v, n1Sel_eq hv']
  refine n1_ite_guard fun hC => ?_
  rw [n1Bit_eq]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hC
  exact n1_testBit_land (n1OrM_of_filter rfl hv' hC.1)
    (n1_testBit_land (n1OrM_of_filter rfl hv' hC.2.1)
    (n1_testBit_land (n1OrM_of_filter rfl hv' hC.2.2.1)
    (n1_testBit_land (n1OrM_of_filter rfl hv' hC.2.2.2.1)
    (n1_testBit_land (n1OrM_of_filter rfl hv' hC.2.2.2.2.1)
    (n1_testBit_land (n1OrM_of_filter rfl hv' hC.2.2.2.2.2.1)
    (n1OrM_of_filter rfl hv' hC.2.2.2.2.2.2))))))

theorem bitV_cbL : ∀ i, 3 ≤ i → i < 6 → ∀ j < 7, ∀ v, bitV (cbL j i) i v = v := by
  intro i hi1 hi2 j hj v
  interval_cases i <;> interval_cases j <;> rfl

@[expose] noncomputable def n1DecF9 (x n : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih x => Nat.land x 511 :: ih (Nat.shiftRight x 9)) n x

@[expose] noncomputable def n1DecF7 (x n : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => ℕ → List ℕ) (fun _ => [])
    (fun _ ih x => Nat.land x 127 :: ih (Nat.shiftRight x 7)) n x

@[expose] noncomputable def n1DecC (x j : ℕ) : List (List ℕ) :=
  Nat.rec (motive := fun _ => ℕ → List (List ℕ)) (fun _ => [])
    (fun _ ih x => n1DecF7 (Nat.shiftRight x 8) (Nat.land x 255) ::
      ih (Nat.shiftRight x (Nat.add 8 (Nat.mul 7 (Nat.land x 255))))) j x

@[expose] noncomputable def n1DecSt (i x : ℕ) : List ℕ × List (List ℕ) :=
  (n1DecF9 x i, n1DecC (Nat.shiftRight x (Nat.mul 9 i)) 7)

@[expose] noncomputable def n1Lv (i : ℕ) : List (List (List (List ℕ × List (List ℕ)))) :=
  (nRaw i).map (·.map (·.map (n1DecSt i)))

theorem n1_land_mod (x w : ℕ) : Nat.land x (2 ^ w - 1) = x % 2 ^ w :=
  Nat.and_two_pow_sub_one_eq_mod x w

theorem n1_shr_div (x w : ℕ) : Nat.shiftRight x w = x / 2 ^ w := Nat.shiftRight_eq_div_pow x w

theorem n1DecF9_eq : ∀ n x, decF 9 x n = n1DecF9 x n := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    have h : n1DecF9 x (n + 1) = Nat.land x (2 ^ 9 - 1) :: n1DecF9 (Nat.shiftRight x 9) n := rfl
    rw [decF, ih, h, n1_land_mod, n1_shr_div]

theorem n1DecF7_eq : ∀ n x, decF 7 x n = n1DecF7 x n := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    have h : n1DecF7 x (n + 1) = Nat.land x (2 ^ 7 - 1) :: n1DecF7 (Nat.shiftRight x 7) n := rfl
    rw [decF, ih, h, n1_land_mod, n1_shr_div]

theorem n1DecC_eq : ∀ j x, decC x j = n1DecC x j := by
  intro j
  induction j with
  | zero => intro x; rfl
  | succ j ih =>
    intro x
    have h : n1DecC x (j + 1) = n1DecF7 (Nat.shiftRight x 8) (Nat.land x (2 ^ 8 - 1)) ::
        n1DecC (Nat.shiftRight x (8 + 7 * Nat.land x (2 ^ 8 - 1))) j := rfl
    have h8 : (2 : ℕ) ^ 8 = 256 := by norm_num
    rw [decC, ih, n1DecF7_eq, h, n1_land_mod, n1_shr_div, n1_shr_div, Nat.pow_add,
      ← Nat.div_div_eq_div_mul, h8]

theorem n1Lv_eq (i : ℕ) : nLv i = n1Lv i := by
  have h : decSt i = n1DecSt i := by
    funext x
    have h' : n1DecSt i x = (n1DecF9 x i, n1DecC (Nat.shiftRight x (9 * i)) 7) := rfl
    rw [decSt, h', n1DecF9_eq, n1DecC_eq, n1_shr_div]
  rw [nLv, n1Lv, h]

@[expose] noncomputable def n1BL {α : Type} (f : α → α → Bool) (a b : List α) : Bool :=
  List.rec (motive := fun _ => List α → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y t _ => bif f x y then ih t else false) b) a b

theorem n1BL_iff {α : Type} {f : α → α → Bool} (hf : ∀ x y, f x y = true ↔ x = y) :
    ∀ a b : List α, n1BL f a b = true ↔ a = b := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b
    · exact ⟨fun _ => rfl, fun _ => rfl⟩
    · exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => nomatch h⟩
  | cons x t ih =>
    intro b
    cases b with
    | nil => exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => nomatch h⟩
    | cons y u =>
      change (bif f x y then n1BL f t u else false) = true ↔ _
      rw [List.cons.injEq, ← hf x y, ← ih u]
      cases f x y
      · exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => (Bool.false_ne_true h.1).elim⟩
      · exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

@[expose] noncomputable def n1BSt (p q : List ℕ × List (List ℕ)) : Bool :=
  bif n1BL Nat.beq p.1 q.1 then n1BL (n1BL Nat.beq) p.2 q.2 else false

theorem n1BS_iff (a b : List (List ℕ × List (List ℕ))) : n1BL n1BSt a b = true ↔ a = b := by
  have hN : ∀ x y : ℕ, Nat.beq x y = true ↔ x = y :=
    fun x y => ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl x⟩
  refine n1BL_iff (fun p q => ?_) a b
  change (bif n1BL Nat.beq p.1 q.1 then n1BL (n1BL Nat.beq) p.2 q.2 else false) = true ↔ _
  rw [Prod.ext_iff, ← n1BL_iff hN p.1 q.1, ← n1BL_iff (n1BL_iff hN) p.2 q.2]
  cases n1BL Nat.beq p.1 q.1
  · exact ⟨fun h => (Bool.false_ne_true h).elim, fun h => (Bool.false_ne_true h.1).elim⟩
  · exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩

@[expose] noncomputable def nStepOKM (i s : ℕ) : Bool :=
  ((((n1Lv i).flatten).getD s []).all fun st => st.1.length == i) &&
    n1BL n1BSt ((((n1Lv i).flatten).getD s []).flatMap (nStepM cbL (vL i) i))
      ((n1Lv (i + 1)).getD s []).flatten

theorem nStepOK_of_M {i : ℕ} (hi1 : 3 ≤ i) (hi2 : i < 6) {s : ℕ} (h : nStepOKM i s = true) :
    nStepOK i s = true := by
  refine nStepOK_of_B (by omega) ?_
  have hvs : ∀ v ∈ vL i, v ∈ vL.vL3 := by
    interval_cases i <;> exact fun v hv => hv
  rw [nStepOKM, ← n1Lv_eq, ← n1Lv_eq, ← nBlocks, Bool.and_eq_true, n1BS_iff] at h
  rw [nStepOKB, Bool.and_eq_true, beq_iff_eq]
  simpa only [funext (nStepB_eq_nStepM hvs (bitV_cbL i hi1 hi2))] using h

set_option maxHeartbeats 0 in
theorem nStep3 : ∀ s < (nBlocks 3).length, nStepOK 3 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 3).length = 1)] at hs
  refine nStepOK_of_M (by norm_num) (by norm_num) ?_
  interval_cases s
  decide +kernel

set_option maxHeartbeats 0 in
theorem nStep4 : ∀ s < (nBlocks 4).length, nStepOK 4 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 4).length = 6)] at hs
  refine nStepOK_of_M (by norm_num) (by norm_num) ?_
  interval_cases s <;> decide +kernel

set_option maxHeartbeats 0 in
theorem nStep5 : ∀ s < (nBlocks 5).length, nStepOK 5 s = true := by
  intro s hs
  rw [(by decide +kernel : (nBlocks 5).length = 96)] at hs
  refine nStepOK_of_M (by norm_num) (by norm_num) ?_
  interval_cases s <;> decide +kernel

end CertificateChecks.KernelO8.SB3871

end
