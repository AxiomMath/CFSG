
module

public import Certificates.Kernel.Misc.GL52.IsoHom
public import CFSG.Literature.GL52IsosInputs
public meta import CFSG.Literature.GL52BFS
public meta import CFSG.Literature.GL52Pass
public meta import CFSG.Literature.GL52Elements
public meta import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import CFSG.Literature.GL52Basic

public section

namespace CertificateChecks.KernelMisc.GL52L

open CFSG CFSG.Literature CFSG.Literature.GL52 Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.KC.Misc.GLM

set_option maxRecDepth 100000

theorem lkMulOK_of {Q : Type*} [Group Q] {K : Type} [DecidableEq K] (gs : List G) (key : Q → K)
    (L : List (K × List ℤ)) (h : ∀ q r : Q, (wK gs (lkWord key L (q * r)) ==
      mmulK (wK gs (lkWord key L q)) (wK gs (lkWord key L r))) = true) : lkMulOK gs key L := by
  intro q r
  change tblEq 31 (wT gs (lkWord key L (q * r)))
    (compT 31 (wT gs (lkWord key L q)) (wT gs (lkWord key L r))) = true
  rw [tblEq_wT_comp]
  exact h q r

theorem lkInjOK_of {Q : Type*} [Group Q] {K : Type} [DecidableEq K] (gs : List G) (key : Q → K)
    (L : List (K × List ℤ)) (h : ∀ q : Q, (wK gs (lkWord key L q) == idK) = true → q = 1) :
    lkInjOK gs key L := by
  intro q hq
  change tblEq 31 (wT gs (lkWord key L q)) (idT 31) = true at hq
  rw [tblEq_wT_id] at hq
  exact h q hq

theorem a5Mul : (tblA5.all fun e => tblA5.all fun e' => lkK gensK1 tblA5 (compKey e.1 e'.1) ==
    mmulK (lkK gensK1 tblA5 e.1) (lkK gensK1 tblA5 e'.1)) = true := by
  quickRfl

theorem a5Inj : (tblA5.all fun e => !(lkK gensK1 tblA5 e.1 == idK) || e.1 == keyA5 1) = true := by
  quickRfl

theorem mulOK_K1' : ∀ q r : alternatingGroup (Fin 5),
    tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 (q * r))
      (compT 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (lkTableT tbK1 tbiK1 keyA5 tblA5 r)) =
      true :=
  mulOK_of gensK1 keyA5 tblA5 compKey keyA5_mul (mem_of_isSome keyA5_mem') a5Mul

theorem injOK_K1' : ∀ q : alternatingGroup (Fin 5),
    tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (idT 31) = true → q = 1 :=
  injOK_of gensK1 keyA5 tblA5 (keyA5 1) (fun _ h => keyA5_inj h) (mem_of_isSome keyA5_mem') a5Inj

theorem gl3Len : tblGL3.length ≤ 21 * 8 := by
  have h : Nat.ble tblGL3.length (21 * 8) = true := by quickRfl
  have h' := Nat.le_of_ble_eq_true h
  exact h'

theorem k2Let : (tblGL3.all fun e => lets3.all fun l =>
    lkK gensK2 tblGL3 (mulKey e.1 (keyGL3 (letQ [gA, gB] l))) ==
      mmulK (lkK gensK2 tblGL3 e.1) (letterK (gK gensK2) (giK gensK2) l)) = true := by
  quickRfl

theorem t2Let : (tblGL3.all fun e => lets3.all fun l =>
    lkK gensT2 tblGL3 (mulKey e.1 (keyGL3 (letQ [gA, gB] l))) ==
      mmulK (lkK gensT2 tblGL3 e.1) (letterK (gK gensT2) (giK gensT2) l)) = true := by
  quickRfl

theorem k2Inj :
    (tblGL3.all fun e => !(lkK gensK2 tblGL3 e.1 == idK) || e.1 == keyGL3 1) = true := by
  quickRfl

theorem mulOK_K2' : ∀ q r : GL (Fin 3) (ZMod 2),
    tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 (q * r))
      (compT 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (lkTableT tbK2 tbiK2 keyGL3 tblGL3 r)) =
      true :=
  fun q r => tblEq_of_lkFun_mul gensK2 keyGL3 tblGL3 q r (gl3_hom gensK2 k2Let q r)

theorem injOK_K2' : ∀ q : GL (Fin 3) (ZMod 2),
    tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (idT 31) = true → q = 1 :=
  injOK_of gensK2 keyGL3 tblGL3 (keyGL3 1) (fun _ h => keyGL3_inj h) keyGL3_mem k2Inj

theorem mulOK_T2' : ∀ q r : GL (Fin 3) (ZMod 2),
    tblEq 31 (lkTableT tbT2 tbiT2 keyGL3 tblGL3 (q * r))
      (compT 31 (lkTableT tbT2 tbiT2 keyGL3 tblGL3 q) (lkTableT tbT2 tbiT2 keyGL3 tblGL3 r)) =
      true :=
  fun q r => tblEq_of_lkFun_mul gensT2 keyGL3 tblGL3 q r (gl3_hom gensT2 t2Let q r)

theorem mulOK_X : lkMulOK gensX (keyPerm (n := 3)) tblS3 :=
  lkMulOK_of gensX (keyPerm (n := 3)) tblS3 (by decide +kernel)

theorem injOK_X : lkInjOK gensX (keyPerm (n := 3)) tblS3 :=
  lkInjOK_of gensX (keyPerm (n := 3)) tblS3 (by decide +kernel)

theorem mulOK_D : lkMulOK gensD keyD8 tblD8 :=
  lkMulOK_of gensD keyD8 tblD8 (by decide +kernel)

theorem injOK_D : lkInjOK gensD keyD8 tblD8 :=
  lkInjOK_of gensD keyD8 tblD8 (by decide +kernel)

theorem mulOK_E : lkMulOK gensE (keyVec (n := 4) (p := 2)) tblE16 :=
  lkMulOK_of gensE (keyVec (n := 4) (p := 2)) tblE16 (by decide +kernel)

theorem injOK_E : lkInjOK gensE (keyVec (n := 4) (p := 2)) tblE16 :=
  lkInjOK_of gensE (keyVec (n := 4) (p := 2)) tblE16 (by decide +kernel)

theorem mulOK_R : lkMulOK r0Gens (keyVec (n := 2) (p := 3)) tblR9 :=
  lkMulOK_of r0Gens (keyVec (n := 2) (p := 3)) tblR9 (by decide +kernel)

theorem injOK_R : lkInjOK r0Gens (keyVec (n := 2) (p := 3)) tblR9 :=
  lkInjOK_of r0Gens (keyVec (n := 2) (p := 3)) tblR9 (by decide +kernel)

theorem mulOK_T1 : lkMulOK gensT1 (keyVec (n := 3) (p := 2)) tblE8 :=
  lkMulOK_of gensT1 (keyVec (n := 3) (p := 2)) tblE8 (by decide +kernel)

theorem holChk0 : (((tblGL3.drop (21 * 0)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk1 : (((tblGL3.drop (21 * 1)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk2 : (((tblGL3.drop (21 * 2)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk3 : (((tblGL3.drop (21 * 3)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk4 : (((tblGL3.drop (21 * 4)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk5 : (((tblGL3.drop (21 * 5)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk6 : (((tblGL3.drop (21 * 6)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk7 : (((tblGL3.drop (21 * 7)).take 21).all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  quickRfl

theorem holChk : (tblGL3.all fun e =>
    tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1))
          (lkK gensT2 tblGL3 e'.1)) = true := by
  refine all_of_chunks _ 21 8 tblGL3 gl3Len fun i hi => ?_
  interval_cases i
  · exact holChk0
  · exact holChk1
  · exact holChk2
  · exact holChk3
  · exact holChk4
  · exact holChk5
  · exact holChk6
  · exact holChk7

theorem holCompat_check : ∀ (M : GL (Fin 3) (ZMod 2)) (c : Multiplicative (Fin 3 → ZMod 2)),
    tblEq 31 (t1Table (glAct M c)) (compT 31 (compT 31 (t2Table M) (t1Table c)) (t2Table M⁻¹)) =
      true := by
  intro M c
  obtain ⟨e, he, hM⟩ := keyGL3_mem M
  obtain ⟨e', he', hM'⟩ := keyGL3_mem M⁻¹
  obtain ⟨ec, hec, hc⟩ := mem_of_isSome keyVec_mem' c
  have h₁ : (tblGL3.all fun e' => !(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1)) (lkK gensT2 tblGL3 e'.1)) =
      true :=
    List.all_eq_true.1 holChk e he
  have h₂ : (!(mulKey e.1 e'.1 == keyGL3 1) || tblE8.all fun c =>
      lkK gensT1 tblE8 (mulVecKey e.1 c.1) ==
        mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 c.1)) (lkK gensT2 tblGL3 e'.1)) =
      true :=
    List.all_eq_true.1 h₁ e' he'
  have hk : mulKey e.1 e'.1 = keyGL3 1 := by
    rw [hM, hM', ← keyGL3_mul, mul_inv_cancel]
  rw [hk, beq_self_eq_true, Bool.not_true, Bool.false_or] at h₂
  have h₃ : (lkK gensT1 tblE8 (mulVecKey e.1 ec.1) ==
      mmulK (mmulK (lkK gensT2 tblGL3 e.1) (lkK gensT1 tblE8 ec.1)) (lkK gensT2 tblGL3 e'.1)) =
      true :=
    List.all_eq_true.1 h₂ ec hec
  change tblEq 31 (wT gensT1 (lkW tblE8 (keyVec (glAct M c))))
    (compT 31 (compT 31 (wT gensT2 (lkW tblGL3 (keyGL3 M))) (wT gensT1 (lkW tblE8 (keyVec c))))
      (wT gensT2 (lkW tblGL3 (keyGL3 M⁻¹)))) = true
  rw [tblEq_wT_comp3, keyVec_glAct, ← hM, ← hc, ← hM']
  exact h₃

theorem holInj_check : ∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
    tblEq 31 (compT 31 (t1Table c) (t2Table M)) (idT 31) = true → c = 1 ∧ M = 1 := by
  have h : (([] :: tblE8.map Prod.snd).all fun w₁ => ([] :: tblGL3.map Prod.snd).all fun w₂ =>
      !(mmulK (wK gensT1 w₁) (wK gensT2 w₂) == idK) || (w₁.isEmpty && w₂.isEmpty)) = true := by
    quickRfl
  intro c M hc
  have h₁ : (([] :: tblGL3.map Prod.snd).all fun w₂ =>
      !(mmulK (wK gensT1 (lkWord keyVec tblE8 c)) (wK gensT2 w₂) == idK) ||
        ((lkWord keyVec tblE8 c).isEmpty && w₂.isEmpty)) = true :=
    List.all_eq_true.1 h _ (lkWord_mem keyVec tblE8 c)
  have h₂ : (!(mmulK (wK gensT1 (lkWord keyVec tblE8 c)) (wK gensT2 (lkWord keyGL3 tblGL3 M)) ==
      idK) || ((lkWord keyVec tblE8 c).isEmpty && (lkWord keyGL3 tblGL3 M).isEmpty)) = true :=
    List.all_eq_true.1 h₁ _ (lkWord_mem keyGL3 tblGL3 M)
  change tblEq 31 (compT 31 (wT gensT1 (lkWord keyVec tblE8 c))
    (wT gensT2 (lkWord keyGL3 tblGL3 M))) (idT 31) = true at hc
  rw [tblEq_comp_id] at hc
  rw [hc] at h₂
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at h₂
  exact ⟨vec_one c h₂.1, gl3_one M h₂.2⟩

open Certificates in
open CFSG CFSG.Literature CFSG.Literature.GL52 Matrix CFSG.Sporadic.Th CFSG.Sporadic.Th.Native in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem facts2001 : ((gl3Elems.map keyGL3).Nodup ∧ gl3Elems.length = 168)
    ∧ (∀ q r : alternatingGroup (Fin 5),
      tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 (q * r))
        (compT 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (lkTableT tbK1 tbiK1 keyA5 tblA5 r)) =
        true
    )
    ∧ (∀ q : alternatingGroup (Fin 5),
      tblEq 31 (lkTableT tbK1 tbiK1 keyA5 tblA5 q) (idT 31) = true → q = 1
    )
    ∧ (∀ q r : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 (q * r))
        (compT 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (lkTableT tbK2 tbiK2 keyGL3 tblGL3 r)) =
        true
    )
    ∧ (∀ q : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbK2 tbiK2 keyGL3 tblGL3 q) (idT 31) = true → q = 1
    )
    ∧ (lkMulOK gensX (keyPerm (n := 3)) tblS3)
    ∧ (lkInjOK gensX (keyPerm (n := 3)) tblS3)
    ∧ (lkMulOK gensD keyD8 tblD8)
    ∧ (lkInjOK gensD keyD8 tblD8)
    ∧ (lkMulOK gensE (keyVec (n := 4) (p := 2)) tblE16)
    ∧ (lkInjOK gensE (keyVec (n := 4) (p := 2)) tblE16)
    ∧ (lkMulOK r0Gens (keyVec (n := 2) (p := 3)) tblR9)
    ∧ (lkInjOK r0Gens (keyVec (n := 2) (p := 3)) tblR9)
    ∧ (lkMulOK gensT1 (keyVec (n := 3) (p := 2)) tblE8)
    ∧ (∀ q r : GL (Fin 3) (ZMod 2),
      tblEq 31 (lkTableT tbT2 tbiT2 keyGL3 tblGL3 (q * r))
        (compT 31 (lkTableT tbT2 tbiT2 keyGL3 tblGL3 q) (lkTableT tbT2 tbiT2 keyGL3 tblGL3 r)) =
        true
    )
    ∧ (∀ (M : GL (Fin 3) (ZMod 2)) (c : Multiplicative (Fin 3 → ZMod 2)),
      tblEq 31 (t1Table (glAct M c)) (compT 31 (compT 31 (t2Table M) (t1Table c)) (t2Table M⁻¹)) =
        true
    )
    ∧ (∀ (c : Multiplicative (Fin 3 → ZMod 2)) (M : GL (Fin 3) (ZMod 2)),
      tblEq 31 (compT 31 (t1Table c) (t2Table M)) (idT 31) = true → c = 1 ∧ M = 1
    ) :=
  ⟨gl3Elems_ok, mulOK_K1', injOK_K1', mulOK_K2', injOK_K2', mulOK_X, injOK_X, mulOK_D, injOK_D,
    mulOK_E, injOK_E, mulOK_R, injOK_R, mulOK_T1, mulOK_T2', holCompat_check, holInj_check⟩

end CertificateChecks.KernelMisc.GL52L

end
