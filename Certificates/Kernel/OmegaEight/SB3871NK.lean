module

public import Certificates.Kernel.OmegaEight.SB3871N
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] noncomputable def xorK (n : ℕ) : List ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => List ℕ → ℕ → ℕ) (fun _ _ => 0)
    (fun _ ih L c => Nat.xor (nIf(Nat.beq (Nat.land c 1) 1, L.headD 0, 0))
      (ih L.tail (Nat.shiftRight c 1))) n

theorem xorBits_succ' (n : ℕ) (f : ℕ → ℕ) (c : ℕ) : xorBits (n + 1) f c =
    (if c.testBit 0 then f 0 else 0) ^^^ xorBits n (fun j => f (j + 1)) (c / 2) := by
  induction n with
  | zero => simp [xorBits_succ, xorBits]
  | succ n ih =>
    rw [xorBits_succ, ih, xorBits_succ, Nat.xor_assoc, Nat.testBit_succ]

theorem xorBits_eq_xorK (n : ℕ) (L : List ℕ) (c : ℕ) :
    xorBits n (fun l => L.getD l 0) c = xorK n L c := by
  induction n generalizing L c with
  | zero => rfl
  | succ n ih =>
    have h1 : (fun j => L.getD (j + 1) 0) = fun j => L.tail.getD j 0 := by
      funext j
      cases L <;> simp
    have h2 : Nat.shiftRight c 1 = c / 2 := by rw [shr_eq]; rfl
    have h3 : Nat.land c 1 = c % 2 := Nat.and_one_is_mod c
    rw [xorBits_succ', h1, ih]
    change _ = Nat.xor _ (xorK n L.tail (Nat.shiftRight c 1))
    rw [h2, h3, Nat.testBit_zero]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> cases L <;> simp [h] <;> rfl

@[expose] noncomputable def nStepV (q : ℕ) (M cb : ℕ → ℕ → ℕ) (vs : List ℕ) (i : ℕ)
    (st : List ℕ × List (List ℕ)) : List (List ℕ × List (List ℕ)) :=
  vs.filterMap fun v =>
    let Vs := st.1 ++ [v]
    let newc := (List.range q).map fun j =>
      (st.2.getD j []).filter fun e => M e v == xorK (i + 1) Vs (cb j i)
    if newc.all (fun l => !l.isEmpty) then some (Vs, newc) else none

theorem nStep_eq_nStepV (n q : ℕ) (M cb : ℕ → ℕ → ℕ) (olen : ℕ → ℕ) (i : ℕ) :
    nStep n q M cb olen i =
      nStepV q M cb ((List.range (2 ^ n)).filter fun v => v != 0 && olen v == olen (2 ^ i)) i := by
  funext st
  unfold nStep nStepV
  simp only [xorBits_eq_xorK]

@[expose] def cbT : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 65, 130, 264], [1, 2, 5, 8, 17, 32, 64, 139, 256],
    [1, 2, 4, 8, 17, 34, 64, 137, 256], [1, 2, 4, 8, 19, 32, 72, 139, 264],
    [1, 2, 4, 9, 16, 32, 64, 144, 320], [1, 3, 4, 8, 16, 52, 64, 196, 256],
    [1, 2, 4, 10, 16, 32, 80, 128, 432]]

@[expose] noncomputable def cbL (j i : ℕ) : ℕ :=
  bif Nat.blt j 7 && Nat.blt i 9 then (cbT.getD j []).getD i 0 else cbK j i

theorem cbT_ok : ((List.range 7).all fun j => (List.range 9).all fun i =>
    cbK j i == (cbT.getD j []).getD i 0) = true := by
  decide +kernel

theorem cbK_eq_cbL : cbK = cbL := by
  funext j i
  unfold cbL
  cases h : (Nat.blt j 7 && Nat.blt i 9)
  · rfl
  · rw [Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
    rw [cond_true]
    have := List.all_eq_true.1 (List.all_eq_true.1 cbT_ok j (List.mem_range.2 h.1)) i
      (List.mem_range.2 h.2)
    exact beq_iff_eq.1 this

@[expose] def vL : ℕ → List ℕ
  | 0 => [1]
  | 1 => [2, 3, 4, 5, 6, 7]
  | 2 => [2, 3, 4, 5, 6, 7]
  | 3 => vL3
  | 4 => vL3
  | 5 => vL3
  | 6 => vL6
  | 7 => [
    128, 129, 130, 131, 136, 137, 138, 139, 144, 145, 146, 147, 152, 153, 154, 155, 160, 161, 162,
    163, 168, 169, 170, 171, 176, 177, 178, 179, 184, 185, 186, 187, 196, 197, 198, 199, 204, 205,
    206, 207, 212, 213, 214, 215, 220, 221, 222, 223, 224, 225, 226, 227, 232, 233, 234, 235, 240,
    241, 242, 243, 248, 249, 250, 251, 258, 259, 260, 261, 262, 263, 266, 267, 268, 269, 270, 271,
    322, 323, 324, 325, 326, 327, 330, 331, 332, 333, 334, 335, 434, 435, 436, 437, 438, 439, 440,
    441, 444, 445, 446, 447, 482, 483, 484, 485, 486, 487, 488, 489, 492, 493, 494, 495]
  | 8 => vL6
  | _ => []
where
  vL3 : List ℕ := [
    8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 52, 53, 54, 55]
  vL6 : List ℕ := [
    36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 56, 57, 58, 59, 60, 61, 62,
    63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
    86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 256, 257, 264, 265, 320, 321, 328, 329, 432, 433, 442,
    443, 480, 481, 490, 491]

theorem vL_eq : ∀ i < 9,
    (List.range (2 ^ 9)).filter (fun v => v != 0 && olK v == olK (2 ^ i)) = vL i := by
  intro i hi
  refine beq_iff_eq.1 ?_
  interval_cases i <;> decide +kernel

@[expose] noncomputable def nStepOKV (i s : ℕ) : Bool :=
  ((nBlocks i).getD s []).flatMap (nStepV 7 MK cbL (vL i) i) == ((nLv (i + 1)).getD s []).flatten

theorem nStepOK_eq {i : ℕ} (hi : i < 9) (s : ℕ) : nStepOK i s = nStepOKV i s := by
  rw [nStepOK, nStepOKV, nStep_eq_nStepV, vL_eq i hi, cbK_eq_cbL]

@[expose] noncomputable def strictL {α : Type} (y : ℕ) (k : ℕ → List α) : List α :=
  Nat.rec (motive := fun _ => List α) (k 0) (fun n _ => k (Nat.succ n)) y

theorem strictL_eq {α : Type} (y : ℕ) (k : ℕ → List α) : strictL y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def bitV (c i v : ℕ) : ℕ := nIf(Nat.beq (Nat.land (Nat.shiftRight c i) 1) 1, v, 0)

theorem xorK_succ (n : ℕ) (L : List ℕ) (c : ℕ) : xorK (n + 1) L c =
    Nat.xor (bitV c 0 (L.headD 0)) (xorK n L.tail (Nat.shiftRight c 1)) := rfl

theorem xorK_append : ∀ (n : ℕ) (L : List ℕ) (v c : ℕ), L.length = n →
    xorK (n + 1) (L ++ [v]) c = Nat.xor (xorK n L c) (bitV c n v)
  | 0, [], v, c, _ => by
    rw [xorK_succ]
    change Nat.xor _ 0 = Nat.xor 0 _
    exact (Nat.xor_zero _).trans (Nat.zero_xor _).symm
  | n + 1, x :: t, v, c, h => by
    have hs : Nat.shiftRight (Nat.shiftRight c 1) n = Nat.shiftRight c (n + 1) := by
      change c >>> 1 >>> n = c >>> (n + 1)
      rw [← Nat.shiftRight_add, Nat.add_comm]
    rw [List.cons_append, xorK_succ (n + 1) (x :: (t ++ [v])) c, xorK_succ n (x :: t) c,
      List.tail_cons, List.tail_cons, List.headD_cons, List.headD_cons,
      xorK_append n t v _ (by simpa using h)]
    unfold bitV
    rw [hs]
    change (_ : ℕ) ^^^ ((_ : ℕ) ^^^ (_ : ℕ)) = ((_ : ℕ) ^^^ (_ : ℕ)) ^^^ (_ : ℕ)
    rw [Nat.xor_assoc]

@[expose] noncomputable def nStepB (M cb : ℕ → ℕ → ℕ) (vs : List ℕ) (i : ℕ)
    (st : List ℕ × List (List ℕ)) : List (List ℕ × List (List ℕ)) :=
  strictL (xorK i st.1 (cb 0 i)) fun b0 => strictL (xorK i st.1 (cb 1 i)) fun b1 =>
  strictL (xorK i st.1 (cb 2 i)) fun b2 => strictL (xorK i st.1 (cb 3 i)) fun b3 =>
  strictL (xorK i st.1 (cb 4 i)) fun b4 => strictL (xorK i st.1 (cb 5 i)) fun b5 =>
  strictL (xorK i st.1 (cb 6 i)) fun b6 =>
  vs.filterMap fun v =>
    let Vs := st.1 ++ [v]
    let newc := (List.range 7).map fun j =>
      (st.2.getD j []).filter fun e =>
        M e v == Nat.xor ([b0, b1, b2, b3, b4, b5, b6].getD j 0) (bitV (cb j i) i v)
    if newc.all (fun l => !l.isEmpty) then some (Vs, newc) else none

theorem nStepV_eq_nStepB (M cb : ℕ → ℕ → ℕ) (vs : List ℕ) (i : ℕ) (st : List ℕ × List (List ℕ))
    (h : st.1.length = i) : nStepV 7 M cb vs i st = nStepB M cb vs i st := by
  unfold nStepB
  simp only [strictL_eq]
  have hb : [xorK i st.1 (cb 0 i), xorK i st.1 (cb 1 i), xorK i st.1 (cb 2 i),
      xorK i st.1 (cb 3 i), xorK i st.1 (cb 4 i), xorK i st.1 (cb 5 i), xorK i st.1 (cb 6 i)] =
      (List.range 7).map fun j => xorK i st.1 (cb j i) := rfl
  rw [hb]
  unfold nStepV
  have hc : ∀ v, ((List.range 7).map fun j => (st.2.getD j []).filter fun e =>
      M e v == xorK (i + 1) (st.1 ++ [v]) (cb j i)) = (List.range 7).map fun j =>
      (st.2.getD j []).filter fun e => M e v ==
        Nat.xor (((List.range 7).map fun j => xorK i st.1 (cb j i)).getD j 0) (bitV (cb j i) i v) := by
    intro v
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj
    rw [List.getD_eq_getElem ((List.range 7).map fun j => xorK i st.1 (cb j i)) 0
      (by simpa using hj), List.getElem_map, List.getElem_range,
      xorK_append _ _ _ _ h]
  simp only [hc]

@[expose] noncomputable def nStepOKB (i s : ℕ) : Bool :=
  (((nBlocks i).getD s []).all fun st => st.1.length == i) &&
    (((nBlocks i).getD s []).flatMap (nStepB MK cbL (vL i) i) == ((nLv (i + 1)).getD s []).flatten)

theorem nStepOK_of_B {i : ℕ} (hi : i < 9) {s : ℕ} (h : nStepOKB i s = true) :
    nStepOK i s = true := by
  rw [nStepOKB, Bool.and_eq_true, List.all_eq_true] at h
  rw [nStepOK_eq hi, nStepOKV,
    List.flatMap_congr fun st hst => nStepV_eq_nStepB _ _ _ _ st (beq_iff_eq.1 (h.1 st hst))]
  exact h.2

end CertificateChecks.KernelO8.SB3871

end
