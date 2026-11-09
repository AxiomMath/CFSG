module

public import Certificates.Kernel.StdOdd.ThreeBlow
public import Certificates.Kernel.StdOdd.ValsCmd
public import CFSG.Monster.Existence.StdOdd.P5
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeExt
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeInputs
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeData
public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertSylowThree
public import Certificates.Data.Kernel.StdOdd.SylowThreeVals
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

@[expose] noncomputable def wordFromB (f : ℕ × Bool × Bool → ℕ) (w : List (ℕ × Bool × Bool))
    (acc : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc) (fun l _ ih acc => ih (mulB acc (f l))) w acc

theorem wordLB_eq_wordFromB (codes bits : ℕ) (w : List (ℕ × Bool × Bool)) :
    wordLB codes bits w = wordFromB (letLB codes bits) w oneB := rfl

theorem wordTB_eq_wordFromB (codes bits : ℕ) (gam : List ℕ) (w : List (ℕ × Bool × Bool)) :
    wordTB codes bits gam w = wordFromB (twLB codes bits gam) w oneB := rfl

theorem wordFromB_append (f : ℕ × Bool × Bool → ℕ) (a b : List (ℕ × Bool × Bool)) (acc : ℕ) :
    wordFromB f (a ++ b) acc = wordFromB f b (wordFromB f a acc) := by
  induction a generalizing acc with
  | nil => rfl
  | cons l a ih => exact ih _

theorem wordFromB_lt (f : ℕ × Bool × Bool → ℕ) (w : List (ℕ × Bool × Bool)) {acc : ℕ}
    (h : acc < 2 ^ 24336) : wordFromB f w acc < 2 ^ 24336 := by
  induction w generalizing acc with
  | nil => exact h
  | cons l w ih => exact ih (mulB_lt _ _)

theorem decB_wordFromB (f : ℕ × Bool × Bool → ℕ) (w : List (ℕ × Bool × Bool)) (acc : ℕ) :
    decB (wordFromB f w acc) = decB acc * decB (wordFromB f w oneB) := by
  induction w generalizing acc with
  | nil =>
    change decB acc = decB acc * decB oneB
    rw [decB_oneB, mul_one]
  | cons l w ih =>
    change decB (wordFromB f w (mulB acc (f l))) =
      decB acc * decB (wordFromB f w (mulB oneB (f l)))
    rw [ih, ih (mulB oneB (f l)), decB_mulB, decB_mulB, decB_oneB, one_mul, mul_assoc]

theorem wordFromB_conj (f : ℕ × Bool × Bool → ℕ) (g n : List (ℕ × Bool × Bool)) {G Gi : ℕ}
    (hG : wordFromB f g oneB = G) (hGi : wordFromB f g.reverse oneB = Gi) :
    wordFromB f (g ++ n ++ g.reverse) oneB = mulB (wordFromB f n G) Gi := by
  have hb : G < 2 ^ 24336 := by
    rw [← hG]
    exact wordFromB_lt f g oneB_lt
  have hb' := wordFromB_lt f n hb
  rw [wordFromB_append, wordFromB_append, hG, ← hGi]
  exact eq_of_decB_eq (wordFromB_lt f _ hb') (mulB_lt _ _)
    (by rw [decB_mulB]; exact decB_wordFromB f _ _)

theorem GV.chk0 :
    Nat.beq (wordFromB (letLB bracketCodes formBits) gWord oneB) (nthV GV.V 0) = true := by
  quickRfl
theorem GV.chk1 :
    Nat.beq (wordFromB (letLB bracketCodes formBits) gWord.reverse oneB) (nthV GV.V 1) = true := by
  quickRfl
theorem GV.chk2 :
    Nat.beq (wordFromB (twLB bracketCodes formBits gamTable) gWord oneB) (nthV GV.V 2) = true := by
  quickRfl
theorem GV.chk3 : Nat.beq (wordFromB (twLB bracketCodes formBits gamTable) gWord.reverse oneB)
    (nthV GV.V 3) = true := by
  quickRfl

theorem RV.chk : allN 6 (fun k => Nat.beq (mulB (wordFromB (letLB bracketCodes formBits) (nWord k)
    (nthV GV.V 0)) (nthV GV.V 1)) (nthV RV.V k)) = true := by quickRfl
theorem RV.all : ∀ k < 6, Nat.beq (rB k) (nthV RV.V k) = true := by
  intro k hk
  rw [Nat.beq_eq, rB, wordLB_eq_wordFromB, rWord]
  have hG0 := Nat.eq_of_beq_eq_true GV.chk0
  have hG1 := Nat.eq_of_beq_eq_true GV.chk1
  have hc := wordFromB_conj (letLB bracketCodes formBits) gWord (nWord k) hG0 hG1
  exact hc.trans (Nat.eq_of_beq_eq_true (allN_true RV.chk k hk))
theorem EV.chk : allN 5 (fun k => Nat.beq (mulB (wordFromB (letLB bracketCodes formBits) (hWord k)
    (nthV GV.V 0)) (nthV GV.V 1)) (nthV EV.V k)) = true := by quickRfl
theorem EV.all : ∀ k < 5, Nat.beq (eB k) (nthV EV.V k) = true := by
  intro k hk
  rw [Nat.beq_eq, eB, wordLB_eq_wordFromB, eWord]
  have hG0 := Nat.eq_of_beq_eq_true GV.chk0
  have hG1 := Nat.eq_of_beq_eq_true GV.chk1
  have hc := wordFromB_conj (letLB bracketCodes formBits) gWord (hWord k) hG0 hG1
  exact hc.trans (Nat.eq_of_beq_eq_true (allN_true EV.chk k hk))

@[expose] noncomputable def wB (j : ℕ) : ℕ :=
  lineB [lineB RV.V tAidx, lineB RV.V tBidx] (nthLL pwData j)

theorem WV.chk : allN 81 (fun k => Nat.beq (wB k) (nthV WV.V k)) = true := by quickRfl
theorem WV.all : ∀ k < 81, Nat.beq (wB k) (nthV WV.V k) = true :=
  fun k hk => allN_true WV.chk k hk

theorem codes : codesOK bracketCodes = true := by quickRfl
theorem gam : allN 72 (fun j => Nat.blt (nthV gamTable j) 72) = true := by quickRfl
theorem rLt : allN 6 (fun i => ltW (rWord i)) = true := by quickRfl
theorem fixedR : allN 6 (fun i => Nat.beq (mulB (wordFromB (twLB bracketCodes formBits gamTable)
    (nWord i) (nthV GV.V 2)) (nthV GV.V 3)) (nthV RV.V i)) = true := by quickRfl
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
  have h1 : wordTB bracketCodes formBits gamTable (rWord i) = nthV RV.V i := by
    rw [wordTB_eq_wordFromB, rWord]
    have hG2 := Nat.eq_of_beq_eq_true GV.chk2
    have hG3 := Nat.eq_of_beq_eq_true GV.chk3
    have hc := wordFromB_conj (twLB bracketCodes formBits gamTable) gWord (nWord i) hG2 hG3
    exact hc.trans (Nat.eq_of_beq_eq_true (allN_true fixedR i hi))
  have h2 := RV.all i hi
  rw [Nat.beq_eq] at h2 ⊢
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

theorem colsData_getD (i : Fin 6) (j : Fin 5) : colsData.getD (5 * i + j) [] =
    [(colVec i j 0).val, (colVec i j 1).val, (colVec i j 2).val, (colVec i j 3).val,
      (colVec i j 4).val] := by
  have hn : 5 * (i : ℕ) + j < 30 := by omega
  have h1 : Fin.ofNat 6 ((5 * (i : ℕ) + j) / 5) = i := Fin.ext (by rw [Fin.val_ofNat]; omega)
  have h2 : Fin.ofNat 5 ((5 * (i : ℕ) + j) % 5) = j := Fin.ext (by rw [Fin.val_ofNat]; omega)
  simp only [colsData, colVec, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hn, Option.map_some, Option.getD_some, h1, h2, Matrix.mulVec_single_one]
  rfl

open _root_.CFSG.Certificates in
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
  ⟨fixed_r_ok, rWord_lt, conj_ok, colsData_getD, sylow_split, pw_zero⟩

end CFSG.KD.StdOdd.SylowThree

end
