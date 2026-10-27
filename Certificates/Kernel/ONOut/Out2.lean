module

public import CFSG.Certificates.Kernel.ONOut.RowsSound
public import CFSG.Certificates.Kernel.ONOut.InvVSound
public import CFSG.Certificates.Kernel.Spor.Dec3Sound
public import CFSG.Certificates.Kernel.Spor.BytesFSound
public import Certificates.Kernel.ONOut.Checks2
import Certificates.Kernel.Sporadic.BrChain
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelONOut

open CFSG.KC.Ord CFSG.KC.ONOut CFSG.KS.Mat3 CFSG.KS.ONOut CFSG.KD.ONOut CFSG.F3.Native
  CFSG.ComponentClassification.SolMax.ONOut CFSG.Sporadic.ON.Native

local notation "Mt" => mat3 154 23716

theorem hN : (23716 : ℕ) = 154 * 154 := by norm_num

theorem facts : 0 < 154 ∧ 23716 = 154 * 154 ∧ LO = 2 ^ 23716 - 1 ∧ RM = 2 ^ 154 - 1 ∧
    CI = rep1 154 154 ∧ ONE = rep1 (154 + 1) 154 := consts3_facts consts

theorem hLO : LO = 2 ^ 23716 - 1 := facts.2.2.1

theorem hCC : CC = Nat.lor (rep1 154 154) (Nat.shiftLeft (rep1 154 154) 23716) :=
  Nat.eq_of_beq_eq_true ccK

theorem canon_of {X : ℕ} (h : VLD X = true) : Canon3 23716 X := (valid3_iff hLO).1 h

theorem mul_sound {X Y : ℕ} (hX : Canon3 23716 X) (hY : Canon3 23716 Y) :
    Canon3 23716 (MUL X Y) ∧ Mt (MUL X Y) = Mt X * Mt Y := mul3s_sound consts hX hY

theorem mat3_zero : Mt 0 = 0 := by
  funext i j
  simp [mat3, bv]

theorem add_sound {X Y : ℕ} (hX : Canon3 23716 X) (hY : Canon3 23716 Y) :
    Canon3 23716 (addM3 23716 LO X Y) ∧ Mt (addM3 23716 LO X Y) = Mt X + Mt Y := by
  rw [hLO]
  exact addM3_sound hN hX hY

theorem neg_sound {X : ℕ} (hX : Canon3 23716 X) :
    Canon3 23716 (negM3 23716 LO X) ∧ Mt (negM3 23716 LO X) = -Mt X := by
  rw [hLO]
  exact negM3_sound hN hX

theorem z0 : ((0 : Fin 154) : ℕ) = 0 := rfl

theorem rowC_ofFn' (f : ℕ → ℕ) : ∀ i : ℕ, RowC 154 (Array.ofFn (n := 154) fun i : Fin 154 =>
    V.ofFn 154 (fun j => f (154 * i.val + j)))[i]! := by
  intro i
  by_cases hi : i < 154
  · rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    exact rowC_ofFn _ _
  · rw [getElem!_neg _ i (by simpa using hi)]
    exact rowC_zero 154

theorem canonM_ofFn' (f : ℕ → ℕ) : canonM 154 (Array.ofFn (n := 154) fun i : Fin 154 =>
    V.ofFn 154 (fun j => f (154 * i.val + j))) = true :=
  canonM_of (by simp) fun i _ => rowC_ofFn' f i

theorem toMat_ofFn' (f : ℕ → ℕ) (i j : Fin 154) : toMat 154 (Array.ofFn (n := 154) fun i : Fin 154 =>
    V.ofFn 154 (fun j => f (154 * i.val + j))) i j = (f (154 * i.val + j.val) : ZMod 3) := by
  rw [toMat_apply, getElem!_pos _ i.val (by simp), Array.getElem_ofFn, V.val_ofFn,
    if_pos j.isLt]

theorem rowsOf_canon (s : String) : canonM 154 (CFSG.F3.Native.rowsOf 154 s) = true := by
  refine canonM_of (by unfold CFSG.F3.Native.rowsOf; simp) fun i hi => ?_
  unfold CFSG.F3.Native.rowsOf
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact rowC_ofFn _ _

theorem seed3_sound1 {d f N LO RM CI ONE UP lb len M St : Nat} {F : Nat → Nat}
    {cs : List Char} {Cs : List Nat}
    (hr : Nat.beq (decRun3 F lb len d N RM M Cs (nat_lit 1)) St = true)
    (hd : seedDone d (valid3 N LO) M St = true)
    (hc : consts3OK d f N LO RM CI ONE UP = true)
    (hb : CFSG.KS.Bytes.bytesEqK cs F lb len = true)
    (hCs : Cs = List.range ((len + lb - 1) / lb)) :
    CFSG.Blueprint.NativeSporadic.decode 3 d 1 (String.ofList cs) = mat3 d N M :=
  CFSG.KS.Dec3.seed3_sound hc hb hCs hr hd

theorem mA : toMat 154 (rowsA ()) = Mt (MT 0) := by
  have hr := CertificateChecks.KernelSpor.BrChain.run_chain_to
      (run := decRun3 P1 256 24045 154 23716 RM (MT 0)) (fun _ => rfl)
      (fun l₁ l₂ s => CFSG.KS.Dec3.decRun3_append _ _ _ _ _ _ _ l₁ l₂ s) dL (fun k => DA1.getD k 0) 3
      (nat_lit 1) (nat_lit 94867) rfl rfl D1.all
  have h := seed3_sound1 hr d1_end consts (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) r1)
    (by decide +kernel)
  unfold rowsA
  rw [toMat_rowsOf, ONSA.eq, h]

theorem mB : toMat 154 (rowsB ()) = Mt (MT 1) := by
  have hr := CertificateChecks.KernelSpor.BrChain.run_chain_to
      (run := decRun3 P2 256 24045 154 23716 RM (MT 1)) (fun _ => rfl)
      (fun l₁ l₂ s => CFSG.KS.Dec3.decRun3_append _ _ _ _ _ _ _ l₁ l₂ s) dL (fun k => DA2.getD k 0) 3
      (nat_lit 1) (nat_lit 94867) rfl rfl D2.all
  have h := seed3_sound1 hr d2_end consts (CFSG.KS.Bytes.bytesEqK_of_runF (by decide) r2)
    (by decide +kernel)
  unfold rowsB
  rw [toMat_rowsOf, ONSB.eq, h]

theorem cA : canonM 154 (rowsA ()) = true := rowsOf_canon _

theorem cB : canonM 154 (rowsB ()) = true := rowsOf_canon _

theorem trit_of {s : String} {cs : List Char} (hs : s = String.ofList cs)
    (ha : ∀ c ∈ cs, c.toNat < 128) {n : ℕ} (hn : n ≤ 3 * cs.length) {k : ℕ} (hk : k < n) :
    tritAt s.toUTF8 k = tri cs k := by
  subst hs
  exact tritAt_eq ha (by omega)

theorem mN : toMat 154 n0Rows = Mt (MT 2) := by
  obtain ⟨ha, hl, he⟩ := mat27_sound hN dN
  ext i j
  rw [he]
  unfold n0Rows
  rw [toMat_ofFn']
  congr 1
  exact trit_of ONN0.eq ha hl (hN ▸ idx_lt3 i.isLt j.isLt)

theorem cN : canonM 154 n0Rows = true := canonM_ofFn' _

theorem mR : toMat 154 rRows = Mt (MT 3) := by
  obtain ⟨ha, hl, he⟩ := mat27_sound hN dR
  ext i j
  rw [he]
  unfold rRows
  rw [toMat_ofFn']
  congr 1
  exact trit_of ONR.eq ha hl (hN ▸ idx_lt3 i.isLt j.isLt)

theorem cR : canonM 154 rRows = true := canonM_ofFn' _

theorem mV : ∀ i : Fin 154, vVec.val i.val = Mt (MT 4) i 0 := by
  have hm : Nat.land (MT 4) (Nat.lor (rep1 154 154) (Nat.shiftLeft (rep1 154 154) 23716)) = MT 4 := by
    rw [← hCC]
    exact Nat.eq_of_beq_eq_true CFSG.KD.ONOut.mV
  obtain ⟨ha, hl, he⟩ := col27_sound (by norm_num) hN dV hm
  intro i
  rw [he, if_pos z0]
  unfold vVec vecOfCode
  rw [V.val_ofFn, if_pos i.isLt]
  congr 1
  exact trit_of ONV.eq ha hl i.isLt

theorem mU : ∀ j : Fin 154, uVec.val j.val = Mt (MT 5) 0 j := by
  have hm : Nat.land (MT 5) (Nat.lor (2 ^ 154 - 1) (Nat.shiftLeft (2 ^ 154 - 1) 23716)) = MT 5 := by
    rw [← facts.2.2.2.1]
    exact Nat.eq_of_beq_eq_true CFSG.KD.ONOut.mU
  obtain ⟨ha, hl, he⟩ := row27_sound hN dU hm
  intro j
  rw [he, if_pos z0]
  unfold uVec vecOfCode
  rw [V.val_ofFn, if_pos j.isLt]
  congr 1
  exact trit_of ONU.eq ha hl j.isLt

theorem rV : RowC 154 vVec := by unfold vVec vecOfCode; exact rowC_ofFn _ _

theorem rU : RowC 154 uVec := by unfold uVec vecOfCode; exact rowC_ofFn _ _

theorem c0 : Canon3 23716 (MT 0) := canon_of vC0
theorem c1 : Canon3 23716 (MT 1) := canon_of vC1
theorem c2 : Canon3 23716 (MT 2) := canon_of vC2
theorem c3 : Canon3 23716 (MT 3) := canon_of vC3
theorem c4 : Canon3 23716 (MT 4) := canon_of vC4
theorem c5 : Canon3 23716 (MT 5) := canon_of vC5
theorem c6 : Canon3 23716 (MT 6) := canon_of vC6
theorem c7 : Canon3 23716 (MT 7) := canon_of vC7

theorem cAB : Canon3 23716 (MUL (MT 0) (MT 1)) := (mul_sound c0 c1).1

theorem wm_facts : Canon3 23716 WM ∧ Mt WM = (1 + Mt (MT 0) * Mt (MT 1)) +
    -(Mt (MT 0) * Mt (MT 1) * Mt (MT 1)) := by
  have e : WM = addM3 23716 LO (addM3 23716 LO ONE (MUL (MT 0) (MT 1)))
      (negM3 23716 LO (MUL (MUL (MT 0) (MT 1)) (MT 1))) := rfl
  obtain ⟨o1, o2⟩ := one3_sound consts
  obtain ⟨p1, p2⟩ := mul_sound cAB c1
  obtain ⟨s1, s2⟩ := add_sound o1 cAB
  obtain ⟨n1, n2⟩ := neg_sound p1
  obtain ⟨t1, t2⟩ := add_sound s1 n1
  rw [e]
  refine ⟨t1, ?_⟩
  rw [t2, s2, n2, p2, (mul_sound c0 c1).2]
  congr 2

theorem cW : canonM 154 wRows = true := by
  unfold wRows
  have hAB := canonM_mul (canonM_spec cA).1 (RowsWF.of_canonM cA) cB
  have hABB := canonM_mul (by rw [mul_size', (canonM_spec cA).1]) (RowsWF.of_canonM hAB) cB
  exact canonM_addM' (rows_of_canonM (canonM_addM' (rows_of_canonM (canonM_idM 154))
    (rows_of_canonM hAB))) (rows_of_canonM (canonM_negM' hABB))

theorem mW : toMat 154 wRows = Mt WM := by
  unfold wRows
  have hAB := canonM_mul (canonM_spec cA).1 (RowsWF.of_canonM cA) cB
  have hABB := canonM_mul (by rw [mul_size', (canonM_spec cA).1]) (RowsWF.of_canonM hAB) cB
  rw [toMat_addM' (RowsWF.of_canonM (canonM_addM' (rows_of_canonM (canonM_idM 154))
      (rows_of_canonM hAB))) (RowsWF.of_canonM (canonM_negM' hABB)),
    toMat_addM' (RowsWF.of_canonM (canonM_idM 154)) (RowsWF.of_canonM hAB),
    toMat_negM' (canonM_spec hABB).1 (RowsWF.of_canonM hABB),
    toMat_mul (by rw [mul_size', (canonM_spec cA).1]) (RowsWF.of_canonM hAB) (RowsWF.of_canonM cB),
    toMat_mul (canonM_spec cA).1 (RowsWF.of_canonM cA) (RowsWF.of_canonM cB), toMat_idM, mA, mB,
    wm_facts.2]

theorem kernel_check : (okRows rRows && (mulVecRow wRows vVec).beq V.zero &&
    eqM 154 (addM (mul 154 rRows wRows) (outerRows vVec uVec)) (idM 154)) = true := by
  have hWV : Mt WM * Mt (MT 4) = 0 := by
    rw [← (mul_sound wm_facts.1 c4).2, Nat.eq_of_beq_eq_true kW, mat3_zero]
  have h1 : (mulVecRow wRows vVec).beq V.zero = true := by
    refine beq_zero_of (rowC_mulVecRow _ rV.1) fun k hk => ?_
    rw [val_mulVecRow wRows rV.1 ⟨k, hk⟩]
    have e := congrFun (congrFun hWV ⟨k, hk⟩) 0
    rw [Matrix.mul_apply, Matrix.zero_apply] at e
    rw [← e]
    apply Finset.sum_congr rfl
    intro j _
    rw [mW, mV j]
  have hRW := canonM_mul (canonM_spec cR).1 (RowsWF.of_canonM cR) cW
  have hc : canonM 154 (addM (mul 154 rRows wRows) (outerRows vVec uVec)) = true :=
    canonM_addM' (rows_of_canonM hRW) (rows_of_canonM (canonM_outerRows vVec rU))
  have hVU : ∀ i j : Fin 154, (Mt (MT 4) * Mt (MT 5)) i j = vVec.val i * uVec.val j := by
    intro i j
    obtain ⟨-, -, he⟩ := row27_sound hN dU (by
      rw [← facts.2.2.2.1]
      exact Nat.eq_of_beq_eq_true CFSG.KD.ONOut.mU)
    rw [Matrix.mul_apply, Finset.sum_eq_single (0 : Fin 154)
      (fun k _ hk => by
        have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
        rw [he, if_neg hk', mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), mV i, mU j]
  have hm : toMat 154 (addM (mul 154 rRows wRows) (outerRows vVec uVec)) = toMat 154 (idM 154) := by
    rw [toMat_addM' (RowsWF.of_canonM hRW) (RowsWF.of_canonM (canonM_outerRows vVec rU)),
      toMat_mul (canonM_spec cR).1 (RowsWF.of_canonM cR) (RowsWF.of_canonM cW), mR, mW, toMat_idM]
    have hk := Nat.eq_of_beq_eq_true kR
    obtain ⟨q1, q2⟩ := mul_sound c3 wm_facts.1
    obtain ⟨u1, u2⟩ := mul_sound c4 c5
    have hout : toMat 154 (outerRows vVec uVec) = Mt (MT 4) * Mt (MT 5) := by
      ext i j
      rw [hVU, toMat_outerRows rU.1]
    rw [hout, ← q2, ← u2, ← (add_sound q1 u1).2, hk, (one3_sound consts).2]
  rw [okRows_of cR, h1, eqM_of_toMat hc (canonM_idM 154) hm]
  rfl

theorem sq_neg_check : eqM 154 n0SqRows negIdRows = true := by
  have hc := canonM_mul (canonM_spec cN).1 (RowsWF.of_canonM cN) cN
  refine eqM_of_toMat hc (canonM_negM' (canonM_idM 154)) ?_
  unfold n0SqRows negIdRows
  rw [toMat_mul (canonM_spec cN).1 (RowsWF.of_canonM cN) (RowsWF.of_canonM cN), mN,
    toMat_negM' (idM_size' 154) (RowsWF.of_canonM (canonM_idM 154)), toMat_idM,
    ← (mul_sound c2 c2).2, Nat.eq_of_beq_eq_true n2]
  exact (neg3_sound consts).2

@[expose] def spinStep (acc : Array V) (t : ℕ) : Array V :=
  acc.push (mulVecRow (spinGen spinLab[t + 1]!) acc[spinPar[t + 1]!]!)

@[expose] def spinArr (n : ℕ) : Array V := (List.range n).foldl spinStep #[vVec]

theorem spinRows_eq : spinRows = spinArr 153 := rfl

theorem spinArr_succ (n : ℕ) : spinArr (n + 1) = spinStep (spinArr n) n := by
  unfold spinArr
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem spinArr_size : ∀ n, (spinArr n).size = n + 1
  | 0 => rfl
  | n + 1 => by
    rw [spinArr_succ]
    unfold spinStep
    rw [Array.size_push, spinArr_size n]

theorem getElem!_push_lt {a : Array V} {x : V} {i : ℕ} (h : i < a.size) : (a.push x)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by simp; omega), getElem!_pos a i h, Array.getElem_push_lt h]

theorem spinArr_stable {i n : ℕ} (hi : i ≤ n) : ∀ m, n ≤ m → (spinArr m)[i]! = (spinArr n)[i]! := by
  intro m hm
  induction m with
  | zero =>
    rw [show n = 0 by omega]
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hm) with h | h
    · rw [spinArr_succ]
      unfold spinStep
      rw [getElem!_push_lt (by rw [spinArr_size]; omega), ih (by omega)]
    · rw [h]

theorem spinArr_new (n : ℕ) : (spinArr (n + 1))[n + 1]! =
    mulVecRow (spinGen spinLab[n + 1]!) (spinArr n)[spinPar[n + 1]!]! := by
  rw [spinArr_succ]
  unfold spinStep
  have hs := spinArr_size n
  rw [getElem!_pos _ (n + 1) (by simp [hs])]
  simp [Array.getElem_push, hs]

theorem spinRows_zero : spinRows[0]! = vVec := by
  rw [spinRows_eq, spinArr_stable (Nat.le_refl 0) 153 (by omega)]
  rfl

theorem tPar : (List.range 153).all (fun t => decide (spinPar[t + 1]! < t + 1) &&
    decide (spinLab[t + 1]! < 2)) = true := by decide

theorem par_lt {t : ℕ} (ht : t < 153) : spinPar[t + 1]! < t + 1 ∧ spinLab[t + 1]! < 2 := by
  have := List.all_eq_true.1 tPar t (List.mem_range.2 ht)
  simpa using this

theorem spinRows_succ {t : ℕ} (ht : t < 153) : spinRows[t + 1]! =
    mulVecRow (spinGen spinLab[t + 1]!) spinRows[spinPar[t + 1]!]! := by
  rw [spinRows_eq, spinArr_stable (Nat.le_refl (t + 1)) 153 (by omega), spinArr_new,
    spinArr_stable (Nat.le_of_lt_succ (par_lt ht).1) 153 (by omega)]

theorem spin_at {t : ℕ} (h1 : 1 ≤ t) (h2 : t < 154) :
    Nat.beq (MUL (nIf(Nat.beq (labF t) (nat_lit 0), MT 0, MT 1)) (colM3 CC (MT 6) (parF t)))
      (colM3 CC (MT 6) t) = true := by
  have key : ∀ lo n, spinK MUL (MT 0) (MT 1) (MT 6) CC parF labF lo n = true → lo ≤ t →
      t < lo + n → Nat.beq (MUL (nIf(Nat.beq (labF t) (nat_lit 0), MT 0, MT 1))
        (colM3 CC (MT 6) (parF t))) (colM3 CC (MT 6) t) = true := by
    intro lo n h ha hb
    have := spinK_spec n h (t - lo) (by omega)
    rwa [Nat.add_sub_cancel' ha] at this
  have hq : (t - 1) / 16 < 10 := by omega
  refine key (16 * ((t - 1) / 16) + 1) (min 16 (153 - 16 * ((t - 1) / 16))) (SP.all _ hq)
    (by omega) ?_
  rw [Nat.min_def]
  split <;> omega

theorem col_at {X t : ℕ} (hX : Canon3 23716 X) (ht : t < 154) (i : Fin 154) :
    Mt (colM3 CC X t) i 0 = Mt X i ⟨t, ht⟩ := by
  rw [hCC, (colM3_sound (by norm_num) hN hX ht).2 i 0, if_pos z0]

theorem gen_mat (l : ℕ) : toMat 154 (spinGen l) = Mt (nIf(Nat.beq l (nat_lit 0), MT 0, MT 1)) ∧
    canonM 154 (spinGen l) = true ∧ Canon3 23716 (nIf(Nat.beq l (nat_lit 0), MT 0, MT 1)) := by
  unfold spinGen
  by_cases hl : l = 0
  · subst hl
    exact ⟨mA, cA, c0⟩
  · have e : Nat.beq l 0 = false := by
      cases l with
      | zero => exact absurd rfl hl
      | succ l => rfl
    rw [if_neg hl, e]
    exact ⟨mB, cB, c1⟩

theorem spin_val : ∀ t (ht : t < 154), RowC 154 spinRows[t]! ∧
    ∀ k : Fin 154, spinRows[t]!.val k.val = Mt (MT 6) k ⟨t, ht⟩ := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    rcases t with _ | t
    · rw [spinRows_zero]
      refine ⟨rV, fun k => ?_⟩
      rw [mV k, ← Nat.eq_of_beq_eq_true sp0, col_at c6 (by norm_num) k]
    · obtain ⟨hp, -⟩ := par_lt (t := t) (by omega)
      obtain ⟨ihr, ihv⟩ := ih _ hp (by omega)
      rw [spinRows_succ (by omega)]
      refine ⟨rowC_mulVecRow _ ihr.1, fun k => ?_⟩
      obtain ⟨g1, -, g3⟩ := gen_mat spinLab[t + 1]!
      have hpc : spinPar[t + 1]! < 154 := by omega
      have hcol := colM3_sound (by norm_num) hN c6 hpc
      rw [← hCC] at hcol
      have e := congrFun (congrFun (mul_sound g3 hcol.1).2 k) 0
      have hs := Nat.eq_of_beq_eq_true (spin_at (t := t + 1) (by omega) ht)
      change MUL (nIf(Nat.beq spinLab[t + 1]! (nat_lit 0), MT 0, MT 1))
        (colM3 CC (MT 6) spinPar[t + 1]!) = colM3 CC (MT 6) (t + 1) at hs
      rw [hs, col_at c6 ht k, Matrix.mul_apply] at e
      rw [val_mulVecRow _ ihr.1 k, e, g1]
      apply Finset.sum_congr rfl
      intro j _
      rw [ihv j, col_at c6 hpc j]

theorem cS : canonM 154 spinRows = true :=
  canonM_of (by rw [spinRows_eq, spinArr_size]) fun i hi => (spin_val i hi).1

theorem mS : toMat 154 spinRows = (Mt (MT 6)).transpose := by
  ext i j
  rw [toMat_apply, (spin_val i.val i.isLt).2 j, Matrix.transpose_apply]

theorem comm_of {d : ℕ} {A B : Matrix (Fin d) (Fin d) (ZMod 3)} (h : A * B = 1) : B * A = 1 :=
  mul_eq_one_comm.1 h

theorem beq_self (a : V) : a.beq a = true := by simp [V.beq]

theorem spin_check : (spinRows.size == 154 && spinRows[0]!.beq vVec &&
    (List.range 153).all (fun t => decide (spinPar[t + 1]! < t + 1) &&
      decide (spinLab[t + 1]! < 2) &&
      spinRows[t + 1]!.beq (mulVecRow (spinGen spinLab[t + 1]!) spinRows[spinPar[t + 1]!]!)) &&
    okRows spinInvRows && eqM 154 (mul 154 spinInvRows spinRows) (idM 154)) = true := by
  have hI : Mt (MT 7) * Mt (MT 6) = 1 := by
    rw [← (mul_sound c7 c6).2, Nat.eq_of_beq_eq_true spI, (one3_sound consts).2]
  have hinv : toMat 154 spinRows * (Mt (MT 7)).transpose = 1 := by
    rw [mS, ← Matrix.transpose_mul, hI, Matrix.transpose_one]
  obtain ⟨i1, i2⟩ := invV_sound cS hinv
  have i1' : canonM 154 spinInvRows = true := i1
  have hall : (List.range 153).all (fun t => decide (spinPar[t + 1]! < t + 1) &&
      decide (spinLab[t + 1]! < 2) &&
      spinRows[t + 1]!.beq (mulVecRow (spinGen spinLab[t + 1]!) spinRows[spinPar[t + 1]!]!)) = true := by
    rw [List.all_eq_true]
    intro t ht
    have ht' := List.mem_range.1 ht
    obtain ⟨p1, p2⟩ := par_lt ht'
    rw [decide_eq_true p1, decide_eq_true p2, spinRows_succ ht', beq_self]
    rfl
  have hm := canonM_mul (canonM_spec i1).1 (RowsWF.of_canonM i1) cS
  have he : eqM 154 (mul 154 spinInvRows spinRows) (idM 154) = true := by
    refine eqM_of_toMat hm (canonM_idM 154) ?_
    unfold spinInvRows
    have hI' := comm_of hI
    rw [toMat_mul (canonM_spec i1).1 (RowsWF.of_canonM i1) (RowsWF.of_canonM cS), i2, mS,
      ← Matrix.transpose_mul, hI', Matrix.transpose_one, toMat_idM]
  have hsz : spinRows.size = 154 := by rw [spinRows_eq, spinArr_size]
  rw [hsz, spinRows_zero, beq_self, hall, okRows_of i1', he]
  rfl

theorem facts22232 :
    (okRows rRows && (mulVecRow wRows vVec).beq V.zero &&
      eqM 154 (addM (mul 154 rRows wRows) (outerRows vVec uVec)) (idM 154)) = true ∧
    (spinRows.size == 154 && spinRows[0]!.beq vVec &&
      (List.range 153).all (fun t => decide (spinPar[t + 1]! < t + 1) &&
        decide (spinLab[t + 1]! < 2) &&
        spinRows[t + 1]!.beq (mulVecRow (spinGen spinLab[t + 1]!) spinRows[spinPar[t + 1]!]!)) &&
      okRows spinInvRows && eqM 154 (mul 154 spinInvRows spinRows) (idM 154)) = true ∧
    eqM 154 n0SqRows negIdRows = true :=
  ⟨kernel_check, spin_check, sq_neg_check⟩

end CertificateChecks.KernelONOut

end
