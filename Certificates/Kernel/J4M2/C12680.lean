module

public import Certificates.Kernel.J4M2.C12680Checks
public import Certificates.Kernel.J4M2.C12607
public import CFSG.Certificates.Kernel.J4SlpSparseSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelC12680

open CFSG.KC.Enum CFSG.KC.J4Q CFSG.KC.Loop CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KC.J4Sp
  CertificateChecks.KernelSporSch.J4E7 CertificateChecks.KernelJ4Gam
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
  CFSG.AGLEmbeddingD2.Wilson.Coordinator

theorem getN_eq (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], i => by cases i <;> rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getN_eq d l i

section Words

variable {gs : Array Pair} {fs ss : List Nat} (hf : fs.length = gs.size) (hs : ss.length = gs.size)
  (hg : ∀ i < gs.size, PairOK gs[i]! (getN one fs i) (getN one ss i))
include hf hs hg

theorem getD_ok (i : Nat) : PairOK (gs.getD i oneP) (getN one fs i) (getN one ss i) := by
  by_cases hi : i < gs.size
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some,
      ← getElem!_pos gs i hi]
    exact hg i hi
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      getN_eq, getN_eq, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    exact oneP_ok hK

theorem letterPL_ok (l : Int) :
    PairOK (letterPL gs l) (letQ one fs ss l).1 (letQ one fs ss l).2 := by
  unfold letterPL letQ
  by_cases h : 0 < l
  · rw [if_pos h, if_pos h]
    exact getD_ok hf hs hg _
  · rw [if_neg h, if_neg h]
    exact invP_ok (getD_ok hf hs hg _)

theorem wordPL_ok : ∀ w : List Int,
    PairOK (wordPL gs w) (wordQ c rm one fs ss w).1 (wordQ c rm one fs ss w).2
  | [] => oneP_ok hK
  | l :: w => by
    change PairOK (mulP (letterPL gs l) (wordPL gs w)) _ _
    exact mulP_ok hK (letterPL_ok hf hs hg l) (wordPL_ok w)

end Words

theorem etaN_ok {us : Nat → Nat × Nat} (hu : ∀ j, PairOK (uJn j) (us j).1 (us j).2) (n cc : Nat) :
    PairOK (etaN n cc) (etaQ c rm one us n cc).1 (etaQ c rm one us n cc).2 := by
  unfold etaN etaQ
  suffices h : ∀ (l : List Nat) (acc : Pair) (a : Nat × Nat), PairOK acc a.1 a.2 →
      PairOK (l.foldl (fun acc j => if cc.testBit j then mulP acc (uJn j) else acc) acc)
        (l.foldl (fun acc j => if cc.testBit j then mulQ c rm acc (us j) else acc) a).1
        (l.foldl (fun acc j => if cc.testBit j then mulQ c rm acc (us j) else acc) a).2 from
    h _ _ _ (oneP_ok hK)
  intro l
  induction l with
  | nil => intro acc a h; exact h
  | cons j l ih =>
    intro acc a h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih
    by_cases hb : cc.testBit j = true
    · rw [if_pos hb, if_pos hb]
      exact mulP_ok hK h (hu j)
    · rw [if_neg hb, if_neg hb]
      exact h

theorem hxj (k : Nat) (hk : k < 3) : PairOK (xJn k) (P k).1 (P k).2 := by
  have hw := wordPL_ok (gs := #[An, Bn]) (fs := [A, B]) (ss := [A, Bi]) rfl rfl (fun i hi => by
    change i < 2 at hi
    interval_cases i
    · exact pAn
    · exact pBn) (CFSG.Sporadic.J4.Native.localWords.getD k [])
  have h := c12680_xj
  unfold andB at h
  interval_cases k
  · cases h0 : eqP (P 0) (XJF 0) <;> rw [h0] at h
    · cases h
    · exact pairOK_of hw h0
  · cases h0 : eqP (P 0) (XJF 0) <;> rw [h0] at h
    · cases h
    cases h1 : eqP (P 1) (XJF 1) <;> rw [h1] at h
    · cases h
    · exact pairOK_of hw h1
  · cases h0 : eqP (P 0) (XJF 0) <;> rw [h0] at h
    · cases h
    cases h1 : eqP (P 1) (XJF 1) <;> rw [h1] at h
    · cases h
    · exact pairOK_of hw h

theorem hxjs : ∀ i < xJns.size, PairOK xJns[i]! (getN one [(P 0).1, (P 1).1, (P 2).1] i)
    (getN one [(P 0).2, (P 1).2, (P 2).2] i) := fun i hi => by
  change i < 3 at hi
  interval_cases i
  · exact hxj 0 (by omega)
  · exact hxj 1 (by omega)
  · exact hxj 2 (by omega)

theorem huJ (j : Nat) : PairOK (uJn j) (UQ j).1 (UQ j).2 :=
  wordPL_ok rfl rfl hxjs _

theorem hgam : PairOK gamN (P 3).1 (P 3).2 := by
  have hh : PairOK hWn HW.1 HW.2 := wordPL_ok (gs := #[An, Bn]) (fs := [A, B]) (ss := [A, Bi])
    rfl rfl (fun i hi => by
      change i < 2 at hi
      interval_cases i
      · exact pAn
      · exact pBn) _
  have hz : PairOK z0n (etaQ c rm one UQ 11 1131).1 (etaQ c rm one UQ 11 1131).2 :=
    etaN_ok huJ 11 1131
  exact pairOK_of (mulP_ok hK (powP_ok hK (mulP_ok hK hz (mulP_ok hK (mulP_ok hK hh
    (powP_ok hK hH2 20)) (invP_ok hh))) 6) hh) c12680_gam

theorem hgen : ∀ i < gen5n.size, PairOK gen5n[i]! (getN one FS i) (getN one SS i) := fun i hi => by
  change i < 5 at hi
  interval_cases i
  · exact hxj 0 (by omega)
  · exact hxj 1 (by omega)
  · exact hxj 2 (by omega)
  · exact pAn
  · exact pBn

theorem hGE (n : Nat) : PairOK (gEn n) (GE n).1 (GE n).2 := wordPL_ok rfl rfl hgen _

theorem hXF {i : Nat} (hi : i < 8) : PairOK (xN.getD i oneP) (XF i).1 (XF i).2 := by
  interval_cases i
  · exact hGE 0
  · exact hGE 1
  · exact mulP_ok hK (hGE 0) (hGE 2)
  · exact mulP_ok hK (hGE 1) (hGE 2)
  · exact mulP_ok hK (mulP_ok hK (hGE 0) (hGE 1)) (hGE 2)
  · exact mulP_ok hK (hGE 1) (hGE 3)
  · exact mulP_ok hK (hGE 2) (hGE 3)
  · exact mulP_ok hK (mulP_ok hK (mulP_ok hK (mulP_ok hK (mulP_ok hK (hGE 15) (hGE 29)) (hGE 1))
      (hGE 7)) (hGE 9)) (hGE 11)

theorem hx {i : Nat} (hi : i < 8) : PairOK (xN.getD i oneP) (P (Nat.add 4 i)).1 (P (Nat.add 4 i)).2 :=
  pairOK_of (hXF hi) (List.all_eq_true.1 c12680_x i (List.mem_range.2 hi))

theorem hg2 {i : Nat} (hi : i < 8) :
    PairOK (g2N (xN.getD i oneP)) (P (Nat.add 12 i)).1 (P (Nat.add 12 i)).2 :=
  pairOK_of (mulP_ok hK hH1 (mulP_ok hK (mulP_ok hK (invP_ok hgam) (hx hi)) hgam))
    (List.all_eq_true.1 c12680_g2 i (List.mem_range.2 hi))

theorem slp_of {i : Nat} (hi : i < 8) {cs : List Char} (ht : slpText i = String.ofList cs)
    (h : runC i cs = true) : slpLt i = true ∧ slpEq i = true := by
  have hn : 3 ≤ slpN.getD i 0 := by interval_cases i <;> decide
  have hs := slpT_sound hK hn hH2 (hg2 hi) pBn h
  have e : slpProg i = (parseSLP (String.ofList cs)).getD [] := by
    unfold slpProg
    rw [ht]
  unfold slpLt slpEq
  rw [e]
  exact hs

theorem slp0 : slpLt 0 = true ∧ slpEq 0 = true := slp_of (by omega) T0.eq c12680_run0
theorem slp1 : slpLt 1 = true ∧ slpEq 1 = true := slp_of (by omega) T1.eq c12680_run1
theorem slp2 : slpLt 2 = true ∧ slpEq 2 = true := slp_of (by omega) T2.eq c12680_run2
theorem slp3 : slpLt 3 = true ∧ slpEq 3 = true := slp_of (by omega) T3.eq c12680_run3
theorem slp4 : slpLt 4 = true ∧ slpEq 4 = true := slp_of (by omega) T4.eq c12680_run4
theorem slp5 : slpLt 5 = true ∧ slpEq 5 = true := slp_of (by omega) T5.eq c12680_run5
theorem slp6 : slpLt 6 = true ∧ slpEq 6 = true := slp_of (by omega) T6.eq c12680_run6
theorem slp7 : slpLt 7 = true ∧ slpEq 7 = true := slp_of (by omega) T7.eq c12680_run7

theorem conj8 : O.conjOK An.1 QXn.1 (qWord 10 0 1).1 = true ∧
    O.conjOK An.1 QYn.1 (qWord 0 10 6).1 = true := by
  have h := c12680_conj
  rw [andB_iff] at h
  exact ⟨conj_of pAn.1 hQX.1 (mulP_ok hK (mulP_ok hK (powP_ok hK hQX 10) (powP_ok hK hQY 0))
      (powP_ok hK hQZ 1)).1 h.1,
    conj_of pAn.1 hQY.1 (mulP_ok hK (mulP_ok hK (powP_ok hK hQX 0) (powP_ok hK hQY 10))
      (powP_ok hK hQZ 6)).1 h.2⟩

open CFSG CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native in
open CFSG.AGLEmbeddingD2.Wilson.Coordinator in
theorem c12680 : (slpLt 0 = true ∧ slpEq 0 = true)
    ∧ (slpLt 1 = true ∧ slpEq 1 = true)
    ∧ (slpLt 2 = true ∧ slpEq 2 = true)
    ∧ (slpLt 3 = true ∧ slpEq 3 = true)
    ∧ (slpLt 4 = true ∧ slpEq 4 = true)
    ∧ (slpLt 5 = true ∧ slpEq 5 = true)
    ∧ (slpLt 6 = true ∧ slpEq 6 = true)
    ∧ (slpLt 7 = true ∧ slpEq 7 = true)
    ∧ (O.conjOK An.1 QXn.1 (qWord 10 0 1).1 = true ∧ O.conjOK An.1 QYn.1 (qWord 0 10 6).1 = true) :=
  ⟨slp0, slp1, slp2, slp3, slp4, slp5, slp6, slp7, conj8⟩

end CertificateChecks.KernelC12680

end
