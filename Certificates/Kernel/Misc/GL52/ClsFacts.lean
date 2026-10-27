module

public import Certificates.Kernel.Misc.GL52.ClsChkRep
public import Certificates.Kernel.Misc.GL52.ClsChkC0
public import Certificates.Kernel.Misc.GL52.ClsChkN
public import Certificates.Kernel.Misc.GL52.ClsLemmas
public import CFSG.Literature.GL52PassInputs
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMisc.GL52K

open CFSG.KC.Misc.GLM CFSG.KC.Ord CFSG.Literature.GL52 CFSG.GH74.KGroups

open CFSG.KC.Misc.KG (andB_iff)

theorem card_G : Nat.card G = 9999360 := by
  rw [card_GL52]
  norm_num

theorem centCard_top_eq (r : G) : centCard (⊤ : Subgroup G) r =
    Nat.card {g : G // ∀ p ∈ [((r : Mat), (r : Mat))], (g : Mat) * p.1 = p.2 * (g : Mat)} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun g => by
    simp only [Subgroup.mem_top, true_and, List.mem_singleton, forall_eq, ← Units.val_mul,
      Units.val_inj])

theorem centCard_top_one : centCard (⊤ : Subgroup G) 1 = Nat.card G :=
  Nat.card_congr ((Equiv.subtypeEquivRight fun g => by simp).trans (Equiv.subtypeUnivEquiv
    fun _ => trivial))

@[expose] def mdec (c : ℕ) : Mat := Matrix.of fun i j => ((c / 2 ^ (5 * (i : ℕ) + j) % 2 : ℕ) : ZMod 2)

@[expose] def ofCodes (c d : ℕ) : G :=
  if h : mdec c * mdec d = 1 ∧ mdec d * mdec c = 1 then ⟨mdec c, mdec d, h.1, h.2⟩ else 1

@[expose] noncomputable def rep : ℕ → G
  | 0 => glT0
  | 1 => glU0
  | 2 => glTau2
  | 3 => glTau1
  | 7 => glF5
  | i => ofCodes (D.repC.getD i 0) (D.repI.getD i 0)

theorem code_rep : ∀ i < 26, mcode ((rep i : G) : Mat) = D.repC.getD i 0 := by
  intro i hi
  interval_cases i <;> decide +kernel

theorem repOK_of (i : ℕ) (hi : i < 26) : repOK i = true := by
  rcases Nat.lt_or_ge i 13 with h | h
  · exact repOK_lo i h
  · have e := repOK_hi (i - 13) (by omega)
    rwa [Nat.sub_add_cancel h] at e

theorem basR_of (i : ℕ) (hi : i < 26) :
    listBeq (elimK (pR i) (25 * (pR i).length) 25).2 (D.basR i) = true := by
  rcases Nat.lt_or_ge i 13 with h | h
  · exact basR_lo i h
  · have e := basR_hi (i - 13) (by omega)
    rw [Nat.sub_add_cancel h] at e
    exact e

theorem chunk0 (c : ℕ) (hc : c < 16) :
    unitCntR (D.basR 0) (0 + c * 8192) 8192 = D.parts0.getD c 0 := by
  refine Nat.eq_of_beq_eq_true ?_
  rcases (by omega : c < 4 ∨ (4 ≤ c ∧ c < 8) ∨ (8 ≤ c ∧ c < 12) ∨ (12 ≤ c ∧ c < 16)) with
    h | h | h | h
  · exact chunk0_a c h
  · have e := chunk0_b (c - 4) (by omega)
    rwa [Nat.sub_add_cancel h.1] at e
  · have e := chunk0_c (c - 8) (by omega)
    rwa [Nat.sub_add_cancel h.1] at e
  · have e := chunk0_d (c - 12) (by omega)
    rwa [Nat.sub_add_cancel h.1] at e

theorem cnt_rep (i : ℕ) (hi : i < 26) : unitCntK (D.basR i) = D.repN.getD i 0 := by
  rcases i with _ | i
  · change unitCntR (D.basR 0) 0 (Nat.pow 2 (D.basR 0).length) = D.repN.getD 0 0
    rw [show Nat.pow 2 (D.basR 0).length = D.parts0.length * 8192 from rfl,
      unitCntR_chunks (D.basR 0) 8192 D.parts0 0 fun c hc => chunk0 c hc]
    rfl
  · exact Nat.eq_of_beq_eq_true (cntR_ok i (by omega))

theorem cent_rep (i : ℕ) (hi : i < 26) :
    centCard (⊤ : Subgroup G) (rep i) = D.repN.getD i 0 := by
  rw [centCard_top_eq]
  exact solCnt_eq _ (by simp only [List.map_cons, List.map_nil, code_rep i hi]; rfl)
    (basR_of i hi) (cnt_rep i hi)

theorem ord_rep (i : ℕ) (hi : i < 26) : orderOf (rep i) = D.repO.getD i 0 := by
  have h := andB_iff.1 (repOK_of i hi)
  have h2 := (andB_iff.1 h.2).1
  have hm : 0 < D.repO.getD i 0 := by simpa [Nat.blt_eq] using h.1
  rw [← code_rep i hi] at h2
  exact (ordK_iff _ hm).1 h2

theorem fix_rep (i : ℕ) (hi : i < 26) :
    fixCount (rep i) = 2 ^ (5 - D.repR.getD i 0) - 1 := by
  have h := Nat.eq_of_beq_eq_true (andB_iff.1 (andB_iff.1 (andB_iff.1 (repOK_of i hi)).2).2).1
  rw [fixCount_eq, rank_add_one, code_rep i hi, h]

theorem inv_rep (i : ℕ) (hi : i < 26) : invS ((rep i : G) : Mat) = D.repV.getD i 0 := by
  have h := Nat.eq_of_beq_eq_true (andB_iff.1 (andB_iff.1 (andB_iff.1 (repOK_of i hi)).2).2).2
  rw [← invK_mcode, code_rep i hi, h]

theorem cls_rep (i : ℕ) (hi : i < 26) : clsSize (rep i) = 9999360 / D.repN.getD i 0 := by
  rw [clsSize, cent_rep i hi, card_G]

theorem fixId : fixCount (1 : G) = 31 := by
  rw [fixCount_eq, rank_add_one, Units.val_one, mcode_one]
  have h : Nat.beq (2 ^ (5 - rankK (Nat.xor idK idK)) - 1) 31 = true := by quickRfl
  exact Nat.eq_of_beq_eq_true h

theorem invId : invS ((1 : G) : Mat) = D.idV := by
  rw [← invK_mcode, Units.val_one, mcode_one, Nat.eq_of_beq_eq_true idV_ok]

theorem clsId : clsSize (1 : G) = 1 := by
  rw [clsSize, centCard_top_one, card_G]

@[expose] noncomputable def rsAll : List G := 1 :: (List.range 26).map rep

@[expose] noncomputable def dataL : List (ℕ × ℕ × ℕ × ℕ) :=
  (1, 31, D.idV, 1) :: (List.range 26).map fun i =>
    (D.repO.getD i 0, 2 ^ (5 - D.repR.getD i 0) - 1, D.repV.getD i 0, 9999360 / D.repN.getD i 0)

theorem data : rsAll.map (fun r => (orderOf r, fixCount r, invS (r : Mat), clsSize r)) =
    dataL := by
  rw [rsAll, dataL, List.map_cons, List.map_map, orderOf_one, fixId, invId, clsId]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi : i < 26 := List.mem_range.1 hi
  simp only [Function.comp_apply, ord_rep i hi, fix_rep i hi, inv_rep i hi, cls_rep i hi]

theorem cent0 : centCard (⊤ : Subgroup G) glT0 = 21504 := cent_rep 0 (by decide)

theorem cent1 : centCard (⊤ : Subgroup G) glU0 = 1536 := cent_rep 1 (by decide)

theorem cent2 : centCard (⊤ : Subgroup G) glTau2 = 504 := cent_rep 2 (by decide)

theorem cent3 : centCard (⊤ : Subgroup G) glTau1 = 180 := cent_rep 3 (by decide)

theorem cent7 : centCard (⊤ : Subgroup G) glF5 = 15 := cent_rep 7 (by decide)

theorem codeTau2 : mcode ((glTau2 : G) : Mat) = D.tau2 := by
  decide +kernel

theorem codeTauB : mcode ((glTauB : G) : Mat) = D.tauB := by
  decide +kernel

theorem codeR0 : r0Elts.map (fun g : G => mcode (g : Mat)) = D.r0C := by
  decide +kernel

theorem r0_nodup : r0Elts.Nodup := by
  refine List.Nodup.of_map (fun g : G => mcode (g : Mat)) ?_
  rw [codeR0]
  decide

theorem r0_length : r0Elts.length = 9 := by
  have h := congrArg List.length codeR0
  rw [List.length_map] at h
  exact h

theorem getD_of_map {α β : Type*} (f : α → β) (d : α) (e : β) :
    ∀ (l : List α) (L : List β), l.map f = L → ∀ i < l.length, L.getD i e = f (l.getD i d)
  | [], _, _, i, h => absurd h (Nat.not_lt_zero _)
  | x :: l, L, hL, i, h => by
    subst hL
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.map_cons, List.getD_cons_succ]
      exact getD_of_map f d e l _ rfl i (by simpa using h)

theorem map_eq_range {α β : Type*} (f : α → β) (d : α) (l : List α) :
    l.map f = (List.range l.length).map fun i => f (l.getD i d) := by
  refine List.ext_getElem (by simp) fun k h1 _ => ?_
  have hk : k < l.length := by simpa using h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

theorem code_r0 (i : ℕ) (hi : i < 9) : mcode ((r0Elts.getD i 1 : G) : Mat) = D.r0C.getD i 0 :=
  (getD_of_map (fun g : G => mcode (g : Mat)) 1 0 r0Elts D.r0C codeR0 i
    (by rw [r0_length]; exact hi)).symm

theorem cZ0Card : Nat.card {g : G // g * glTau2 = glTau2 * g ∧ g * glTauB = glTauB * g} = 9 := by
  have h := solCnt_eq [(((glTau2 : G) : Mat), ((glTau2 : G) : Mat)),
      (((glTauB : G) : Mat), ((glTauB : G) : Mat))] (n := 9)
    (by simp only [List.map_cons, List.map_nil, codeTau2, codeTauB]; rfl) basZ_ok
    (Nat.eq_of_beq_eq_true cntZ_ok)
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    ← Units.val_mul, Units.val_inj]

theorem nOK_of (i j : ℕ) (hi : i < 9) (hj : j < 9) : nOK i j = true := by
  rcases (by omega : i < 3 ∨ (3 ≤ i ∧ i < 6) ∨ (6 ≤ i ∧ i < 9)) with h | h | h
  · exact nOK_a i h j hj
  · have e := nOK_b (i - 3) (by omega) j hj
    rwa [Nat.sub_add_cancel h.1] at e
  · have e := nOK_c (i - 6) (by omega) j hj
    rwa [Nat.sub_add_cancel h.1] at e

theorem cardN (i j : ℕ) (hi : i < 9) (hj : j < 9) :
    Nat.card {g : G // g * glTau2 = r0Elts.getD i 1 * g ∧ g * glTauB = r0Elts.getD j 1 * g} =
      D.nN.getD (9 * i + j) 0 := by
  have h := andB_iff.1 (nOK_of i j hi hj)
  have e := solCnt_eq [(((glTau2 : G) : Mat), ((r0Elts.getD i 1 : G) : Mat)),
      (((glTauB : G) : Mat), ((r0Elts.getD j 1 : G) : Mat))]
    (by simp only [List.map_cons, List.map_nil, codeTau2, codeTauB, code_r0 i hi, code_r0 j hj]
        rfl)
    h.1 (Nat.eq_of_beq_eq_true h.2)
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)).trans e
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
    ← Units.val_mul, Units.val_inj]

theorem map_r0 {β : Type*} (f : G → β) :
    r0Elts.map f = (List.range 9).map fun i => f (r0Elts.getD i 1) := by
  rw [map_eq_range f 1 r0Elts, r0_length]

theorem r0_sum : (r0Elts.map fun a => (r0Elts.map fun b =>
    Nat.card {g : G // g * glTau2 = a * g ∧ g * glTauB = b * g}).sum).sum = 72 := by
  rw [map_r0]
  have e : ∀ i ∈ List.range 9, (r0Elts.map fun b => Nat.card {g : G //
      g * glTau2 = r0Elts.getD i 1 * g ∧ g * glTauB = b * g}).sum =
      ((List.range 9).map fun j => D.nN.getD (9 * i + j) 0).sum := by
    intro i hi
    rw [map_r0]
    congr 1
    exact List.map_congr_left fun j hj =>
      cardN i j (List.mem_range.1 hi) (List.mem_range.1 hj)
  rw [List.map_congr_left e]
  decide

end CertificateChecks.KernelMisc.GL52K

end
