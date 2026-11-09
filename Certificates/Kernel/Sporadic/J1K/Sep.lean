module

public import Certificates.Kernel.Sporadic.J1K.Checks
public import CFSG.Certificates.Kernel.Spor.PChainGens
public import CFSG.Certificates.Kernel.Spor.VOrbSound
public import CFSG.Sporadic.J1.VecSpec
import CFSG.Sporadic.Th.TableSpec
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Algebra.Module.Pi

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.KS.VO CFSG.Sporadic.J1.Native
  CFSG.Sporadic.J1 CFSG.Sporadic.Th.Native Matrix

noncomputable abbrev PJ : List (List Nat) := colMat 7 [[1, 2, 7, 7, 2, 9, 10], [5, 5, 7, 1, 8, 0, 5],
  [2, 1, 5, 8, 7, 3, 2], [5, 4, 8, 6, 6, 10, 0], [2, 1, 9, 1, 10, 8, 9], [4, 4, 4, 0, 9, 2, 1],
  [5, 5, 4, 10, 8, 0, 5]]

noncomputable abbrev YJ : List (List Nat) := [[0, 6, 7, 6, 2, 7, 4], [10, 5, 9, 9, 3, 5, 10],
  [4, 4, 0, 0, 9, 2, 4], [8, 2, 6, 2, 10, 2, 7], [0, 10, 1, 4, 5, 3, 4], [9, 5, 6, 2, 1, 10, 2],
  [2, 2, 7, 0, 0, 8, 6]]

noncomputable abbrev vecJ1 (i : Nat) : Fin 7 → ZMod 11 := toV 11 7 (decV 7 (r32 PT i))

def MatAct (g : Equiv.Perm (Fin 1540)) : Prop :=
  ∃ M : Matrix (Fin 7) (Fin 7) (ZMod 11), ∀ i < 1540,
    M *ᵥ vecJ1 i = vecJ1 (actN g i) ∨ M *ᵥ vecJ1 i = -vecJ1 (actN g i)

theorem matActJ1_one : MatAct 1 :=
  ⟨1, fun i _ => Or.inl (by rw [one_mulVec, actN_one])⟩

theorem matActJ1_mul {g h : Equiv.Perm (Fin 1540)} (hg : MatAct g) (hh : MatAct h) :
    MatAct (g * h) := by
  obtain ⟨M, hM⟩ := hg
  obtain ⟨N, hN⟩ := hh
  refine ⟨M * N, fun i hi => ?_⟩
  rw [← mulVec_mulVec, actN_mul]
  have hj := actN_lt h hi
  rcases hN i hi with e | e <;> rw [e]
  · exact hM _ hj
  · rw [mulVec_neg]
    rcases hM _ hj with e' | e' <;> rw [e']
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)

theorem matActJ1_closure {X : Set (Equiv.Perm (Fin 1540))} (hX : ∀ x ∈ X, MatAct x) :
    ∀ g ∈ Subgroup.closure X, MatAct g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hX x hx
  | one => exact matActJ1_one
  | mul x y _ _ hx hy => exact matActJ1_mul hx hy
  | inv x _ hx =>
    have hp : ∀ e : Nat, MatAct (x ^ e) := by
      intro e
      induction e with
      | zero => rw [pow_zero]; exact matActJ1_one
      | succ e ih => rw [pow_succ]; exact matActJ1_mul ih hx
    have e : x⁻¹ = x ^ (orderOf x - 1) := by
      apply inv_eq_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [e]
    exact hp _

theorem decV_length (c : Nat) : (decV 7 c).length = 7 := by simp [decV]

theorem mvL_lt' (X : List (List Nat)) (v : List Nat) : ∀ x ∈ mvL 11 X v, x < 11 := by
  intro x hx
  simp only [mvL, List.mem_map] at hx
  obtain ⟨_, _, rfl⟩ := hx
  exact Nat.mod_lt _ (by norm_num)

theorem pt_specJ1 {i : Nat} (hi : i < 1540) :
    vorbPtK 11 7 1540 (sgnKey 11) (mA ()) (mB ()) (r32 PT) AL BE i = true :=
  allN_spec orbPt_ok i hi

theorem key_act {X : List (List Nat)} (hX : wfM 7 X = true) {c c' : Nat}
    (h : listEqK (sgnKey 11 (mvL 11 X (decV 7 c))) (decV 7 c') = true) :
    toM 11 7 X *ᵥ toV 11 7 (decV 7 c) = toV 11 7 (decV 7 c') ∨
      toM 11 7 X *ᵥ toV 11 7 (decV 7 c) = -toV 11 7 (decV 7 c') := by
  rw [listEqK_iff] at h
  rw [← toV_mvL hX (decV_length c)]
  unfold sgnKey at h
  split at h
  · exact Or.inl (by rw [h])
  · refine Or.inr ?_
    rw [← h, toV_negL (mvL_lt' X _), neg_neg]

theorem gen_act {i : Nat} (hi : i < 1540) :
    (toM 11 7 (mA ()) *ᵥ vecJ1 i = vecJ1 (r32 AL i) ∨
      toM 11 7 (mA ()) *ᵥ vecJ1 i = -vecJ1 (r32 AL i)) ∧
    (toM 11 7 (mB ()) *ᵥ vecJ1 i = vecJ1 (r32 BE i) ∨
      toM 11 7 (mB ()) *ᵥ vecJ1 i = -vecJ1 (r32 BE i)) := by
  have h := pt_specJ1 hi
  unfold vorbPtK at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact ⟨key_act (by decide +kernel) h.2.2.2.2.1, key_act (by decide +kernel) h.2.2.2.2.2⟩

theorem pmSepJ1 : pmSep 11 7 (Array.ofFn (n := 1540) fun i => decV 7 (r32 PT i.val)) 3 = true :=
  pmSep_of_proj (by norm_num)
    (fun i hi => by
      have h := pt_specJ1 hi
      unfold vorbPtK at h
      simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
      exact lt_of_lt_of_eq (Nat.blt_eq.mp h.1) (by decide))
    (fun i hi => by
      have h := pt_specJ1 hi
      unfold vorbPtK at h
      simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
      exact h.2.1)
    (allN_spec projSort_ok) 3

theorem minor_ne {u w : List Nat} (h : minorNZ 11 7 u w = true) :
    ∃ x y : Fin 7, toV 11 7 u x * toV 11 7 w y ≠ toV 11 7 u y * toV 11 7 w x := by
  unfold minorNZ at h
  simp only [List.any_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ?_⟩
  simp only [toV]
  rw [← Nat.cast_mul, ← Nat.cast_mul]
  intro e
  exact hxy ((ZMod.natCast_eq_natCast_iff' _ _ 11).1 e)

theorem pt_eq_of_smul {i j : Nat} (hi : i < 1540) (hj : j < 1540) {c : ZMod 11}
    (h : vecJ1 j = c • vecJ1 i) : j = i := by
  have hsep := CFSG.Sporadic.Th.parAll_eq_true pmSepJ1
  have key : ∀ a b, a < b → b < 1540 → ∀ u w : Fin 7 → ZMod 11,
      u = toV 11 7 (decV 7 (r32 PT a)) → w = toV 11 7 (decV 7 (r32 PT b)) →
      (∀ x y : Fin 7, u x * w y = u y * w x) → False := by
    intro a b hab hb u w hu hw hm
    have hc := (CFSG.Sporadic.Th.allIn_eq_true.1 (hsep a (by simp; omega))) b (by omega) (by simpa using hb)
    rw [getElem!_pos _ a (by simp; omega), getElem!_pos _ b (by simpa using hb),
      Array.getElem_ofFn, Array.getElem_ofFn] at hc
    obtain ⟨x, y, hxy⟩ := minor_ne hc
    rw [← hu, ← hw] at hxy
    exact hxy (hm x y)
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact (key i j hij hj _ _ rfl rfl fun x y => by
      change vecJ1 i x * vecJ1 j y = vecJ1 i y * vecJ1 j x
      rw [h]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring).elim
  · rfl
  · exact (key j i hij hi _ _ rfl rfl fun x y => by
      change vecJ1 j x * vecJ1 i y = vecJ1 j y * vecJ1 i x
      rw [h]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring).elim

theorem cols_eq (j : Fin 7) :
    (fun i => toM 11 7 PJ i j) = vecJ1 (QL.getD j.val 0) := by
  funext i
  rw [toM_colMat_apply _ i j (by simp)]
  have e : ∀ j : Fin 7, ([[1, 2, 7, 7, 2, 9, 10], [5, 5, 7, 1, 8, 0, 5],
      [2, 1, 5, 8, 7, 3, 2], [5, 4, 8, 6, 6, 10, 0], [2, 1, 9, 1, 10, 8, 9], [4, 4, 4, 0, 9, 2, 1],
      [5, 5, 4, 10, 8, 0, 5]] : List (List Nat)).getD j.val [] = decV 7 (r32 PT (QL.getD j.val 0)) := by
    decide +kernel
  rw [e j]

theorem sep_J1 {X : Set (Equiv.Perm (Fin 1540))}
    (hX : ∀ x ∈ X, (∀ i < 1540, actN x i = r32 AL i) ∨ ∀ i < 1540, actN x i = r32 BE i) :
    ∀ g ∈ Subgroup.closure X, (∀ x ∈ QL, actN g x = x) → g = 1 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  intro g hg hfix
  have hact := matActJ1_closure (fun x hx => by
    rcases hX x hx with h | h
    · exact ⟨_, fun i hi => by rw [h i hi]; exact (gen_act hi).1⟩
    · exact ⟨_, fun i hi => by rw [h i hi]; exact (gen_act hi).2⟩) g hg
  obtain ⟨M, hM⟩ := hact
  have hQ : ∀ t < 8, ∃ c : ZMod 11, M *ᵥ vecJ1 (QL.getD t 0) = c • vecJ1 (QL.getD t 0) := by
    intro t ht
    have hq : QL.getD t 0 ∈ QL := by
      rw [List.getD_eq_getElem _ _ (by simpa [QL] using ht)]
      exact List.getElem_mem _
    have hlt : QL.getD t 0 < 1540 := by interval_cases t <;> decide
    rcases hM _ hlt with e | e <;> rw [hfix _ hq] at e
    · exact ⟨1, by rw [e, one_smul]⟩
    · refine ⟨-1, funext fun k => ?_⟩
      have h1 := congrFun e k
      change (M *ᵥ vecJ1 (QL.getD t 0)) k = -(vecJ1 (QL.getD t 0) k) at h1
      change (M *ᵥ vecJ1 (QL.getD t 0)) k = (-1) * vecJ1 (QL.getD t 0) k
      rw [h1]
      exact (neg_one_mul _).symm
  have hwfY : wfM 7 YJ = true := by decide +kernel
  have hwfP : wfM 7 PJ = true := by decide +kernel
  have hQP : toM 11 7 YJ * toM 11 7 PJ = 1 := by
    rw [← toM_mulL hwfY hwfP, (by decide +kernel : mulL 11 7 YJ PJ = idL 7), toM_idL]
  have hc : ∀ i, (toM 11 7 YJ *ᵥ vecJ1 2) i ≠ 0 := by
    intro i
    rw [← toV_mvL hwfY (decV_length _)]
    exact toV_ne_zero_of_all (by simp [mvL]) (mvL_lt' _ _) (by decide +kernel) i
  obtain ⟨μ, hμ⟩ := eq_smul_one_of_eigen M _ _ hQP (vecJ1 2) hc
    (fun j => by rw [cols_eq j]; exact hQ j.val (by omega)) (hQ 7 (by norm_num))
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hx := hM x x.isLt
  rw [hμ, smul_mulVec, one_mulVec] at hx
  have hgx := actN_lt g x.isLt
  have e : actN g x = x := by
    rcases hx with e | e
    · exact pt_eq_of_smul x.isLt hgx (c := μ) e.symm
    · refine pt_eq_of_smul x.isLt hgx (c := -μ) ?_
      funext k
      have h1 := congrFun e k
      change μ * vecJ1 x k = -(vecJ1 (actN g x) k) at h1
      change vecJ1 (actN g x) k = (-μ) * vecJ1 x k
      calc vecJ1 (actN g x) k = -(-(vecJ1 (actN g x) k)) := (neg_neg _).symm
        _ = -(μ * vecJ1 x k) := by rw [h1]
        _ = (-μ) * vecJ1 x k := (neg_mul _ _).symm
  rw [actN_fin] at e
  exact e

end CertificateChecks.KernelSpor.J1K

end
