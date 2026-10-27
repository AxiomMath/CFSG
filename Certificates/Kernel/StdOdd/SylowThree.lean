module

public import Certificates.Kernel.StdOdd.ThreeBlow
public import Certificates.Kernel.StdOdd.ValsCmd
public import CFSG.Monster.Existence.StdOdd.P5
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeExt
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeInputs
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KD.StdOdd.SylowThree

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
  CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert

set_option maxRecDepth 100000

@[expose] noncomputable def rB (i : ℕ) : ℕ := wordLB bracketCodes formBits (rWord i)

@[expose] noncomputable def eB (j : ℕ) : ℕ := wordLB bracketCodes formBits (eWord j)

#kc_vals RV rB 6
#kc_vals EV eB 5

@[expose] noncomputable def wB (j : ℕ) : ℕ :=
  lineB [lineB RV.V tAidx, lineB RV.V tBidx] (nthLL pwData j)

#kc_vals WV wB 81

theorem codes : codesOK bracketCodes = true := by quickRfl
theorem gam : allN 72 (fun j => Nat.blt (nthV gamTable j) 72) = true := by quickRfl
theorem rLt : allN 6 (fun i => ltW (rWord i)) = true := by quickRfl
theorem fixedR : allN 6 (fun i =>
    Nat.beq (wordTB bracketCodes formBits gamTable (rWord i)) (nthV RV.V i)) = true := by quickRfl
theorem eLt : allN 5 (fun j => ltW (eWord j)) = true := by quickRfl

theorem conj0 : allN 5 (fun j => Nat.beq (mulB (nthV RV.V 0) (nthV EV.V j))
    (mulB (psiB EV.V (nthLL colsData (Nat.add (Nat.mul 5 0) j))) (nthV RV.V 0))) = true := by
  quickRfl
theorem conj1 : allN 5 (fun j => Nat.beq (mulB (nthV RV.V 1) (nthV EV.V j))
    (mulB (psiB EV.V (nthLL colsData (Nat.add (Nat.mul 5 1) j))) (nthV RV.V 1))) = true := by
  quickRfl
theorem conj2 : allN 5 (fun j => Nat.beq (mulB (nthV RV.V 2) (nthV EV.V j))
    (mulB (psiB EV.V (nthLL colsData (Nat.add (Nat.mul 5 2) j))) (nthV RV.V 2))) = true := by
  quickRfl
theorem conj3 : allN 5 (fun j => Nat.beq (mulB (nthV RV.V 3) (nthV EV.V j))
    (mulB (psiB EV.V (nthLL colsData (Nat.add (Nat.mul 5 3) j))) (nthV RV.V 3))) = true := by
  quickRfl
theorem conj4 : allN 5 (fun j => Nat.beq (mulB (nthV RV.V 4) (nthV EV.V j))
    (mulB (psiB EV.V (nthLL colsData (Nat.add (Nat.mul 5 4) j))) (nthV RV.V 4))) = true := by
  quickRfl
theorem conj5 : allN 5 (fun j => Nat.beq (mulB (nthV RV.V 5) (nthV EV.V j))
    (mulB (psiB EV.V (nthLL colsData (Nat.add (Nat.mul 5 5) j))) (nthV RV.V 5))) = true := by
  quickRfl

theorem tA_lt : allL tAidx (fun i => Nat.blt i 6) = true := by quickRfl
theorem tB_lt : allL tBidx (fun i => Nat.blt i 6) = true := by quickRfl
theorem pw_lt : allN 81 (fun j => allL (nthLL pwData j) (fun x => Nat.blt x 2)) = true := by
  quickRfl
theorem ra_lt : allN 81 (fun j => Nat.blt (nthV raData j) 81) = true := by quickRfl
theorem rb_lt : allN 81 (fun j => Nat.blt (nthV rbData j) 81) = true := by quickRfl
theorem tA3 : Nat.beq (powB (lineB RV.V tAidx) 3) oneB = true := by quickRfl
theorem tB3 : Nat.beq (powB (lineB RV.V tBidx) 3) oneB = true := by quickRfl
theorem sA : allN 81 (fun j => Nat.beq (mulB (nthV WV.V j) (lineB RV.V tAidx))
    (nthV WV.V (nthV raData j))) = true := by quickRfl
theorem sB : allN 81 (fun j => Nat.beq (mulB (nthV WV.V j) (lineB RV.V tBidx))
    (nthV WV.V (nthV rbData j))) = true := by quickRfl

theorem getD_range_map {α : Type*} (f : ℕ → α) (d : α) {n i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem rWord_lt : ∀ i < 6, ∀ l ∈ rWord i, l.1 < 72 := fun i hi => ltW_true (allN_true rLt i hi)

theorem eWord_lt : ∀ j < 5, ∀ l ∈ eWord j, l.1 < 72 := fun j hj => ltW_true (allN_true eLt j hj)

theorem mem_range_map {α : Type*} {f : ℕ → α} {n : ℕ} {w : α} (h : w ∈ (List.range n).map f) :
    ∃ i < n, f i = w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  exact ⟨i, List.mem_range.1 hi, rfl⟩

theorem rs_lt : ∀ w ∈ (List.range 6).map rWord, ∀ l ∈ w, l.1 < 72 := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := mem_range_map hw
  exact rWord_lt i hi

theorem es_lt : ∀ w ∈ (List.range 5).map eWord, ∀ l ∈ w, l.1 < 72 := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := mem_range_map hw
  exact eWord_lt i hi

theorem hR : ∀ i < ((List.range 6).map rWord).length,
    Nat.beq (wordLB bracketCodes formBits (((List.range 6).map rWord).getD i [])) (nthV RV.V i) =
      true := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [getD_range_map _ _ hi]
  exact RV.all i hi

theorem hE : ∀ j < ((List.range 5).map eWord).length,
    Nat.beq (wordLB bracketCodes formBits (((List.range 5).map eWord).getD j [])) (nthV EV.V j) =
      true := by
  intro j hj
  simp only [List.length_map, List.length_range] at hj
  rw [getD_range_map _ _ hj]
  exact EV.all j hj

theorem fixed_r_ok :
    CertNative.fixedOK bracketCodes formBits gamTable ((List.range 6).map rWord) = true := by
  refine fixedOK_of codes formBits gam rs_lt fun w hw => ?_
  obtain ⟨i, hi, rfl⟩ := mem_range_map hw
  have h1 := allN_true fixedR i hi
  have h2 := RV.all i hi
  rw [Nat.beq_eq] at h1 h2 ⊢
  exact h1.trans h2.symm

theorem conj_ok : CertNative.conjOK bracketCodes formBits ((List.range 6).map rWord)
    ((List.range 5).map eWord) colsData = true := by
  refine conjOK_of codes formBits rs_lt es_lt (by simp) (by simp) hR hE fun i hi => ?_
  interval_cases i
  exacts [conj0, conj1, conj2, conj3, conj4, conj5]

theorem sylow_split : CertNative.splitOK bracketCodes formBits ((List.range 6).map rWord)
    tAidx tBidx pwData raData rbData = true := by
  have hlen : ((List.range 6).map rWord).length = 6 := by simp
  refine splitOK_of (W := WV.V) codes formBits rs_lt hR (fun i hi => ?_) (fun i hi => ?_) (fun j hj => ?_)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) tA3 tB3 (fun j hj => ?_) (fun j hj => ?_)
  · rw [hlen]
    have h := allL_true tA_lt i hi
    rwa [Nat.blt_eq] at h
  · rw [hlen]
    have h := allL_true tB_lt i hi
    rwa [Nat.blt_eq] at h
  · intro x hx
    rw [← nthLL_eq_getD] at hx
    have h := allL_true (allN_true pw_lt j hj) x hx
    rwa [Nat.blt_eq] at h
  · rw [← nthLL_eq_getD]
    exact WV.all j hj
  · have h := allN_true ra_lt j hj
    rwa [Nat.blt_eq, nthV_eq_getD] at h
  · have h := allN_true rb_lt j hj
    rwa [Nat.blt_eq, nthV_eq_getD] at h
  · rw [← nthV_eq_getD]
    exact allN_true sA j hj
  · rw [← nthV_eq_getD]
    exact allN_true sB j hj

theorem pw_zero : P5.pw 0 = [] := rfl

open Certificates in
open CFSG CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.StdOdd in
open CFSG.Monster.Existence.StdOdd.Cert CFSG.Blueprint.Chevalley in
open CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel in
open CFSG.Monster.B.Classical.E6Adjoint in
open CFSG.Monster.Existence.StdOdd.P5 (E5 GL5 M5 rk refl reflGL genA genB Pbar IsExt) in
theorem facts : (CertNative.fixedOK bracketCodes formBits gamTable
      ((List.range 6).map rWord) = true)
    ∧ (∀ i < 6, ∀ l ∈ rWord i, l.1 < 72)
    ∧ (CertNative.conjOK bracketCodes formBits ((List.range 6).map rWord)
      ((List.range 5).map eWord) colsData = true)
    ∧ (∀ (i : Fin 6) (j : Fin 5), colsData.getD (5 * i + j) [] =
      [(colVec i j 0).val, (colVec i j 1).val, (colVec i j 2).val, (colVec i j 3).val,
        (colVec i j 4).val])
    ∧ (CertNative.splitOK bracketCodes formBits ((List.range 6).map rWord)
      tAidx tBidx pwData raData rbData = true)
    ∧ (P5.pw 0 = []) :=
  ⟨fixed_r_ok, rWord_lt, conj_ok, by decide +kernel, sylow_split, pw_zero⟩

end CFSG.KD.StdOdd.SylowThree

end
