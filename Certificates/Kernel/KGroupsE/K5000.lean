module

public import CFSG.GH74.AS16.E2.Local3ChecksInputs
public import CFSG.GH74.KGroups.M11TablesInputs
public import CFSG.GH74.KGroups.L33TablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
public import Certificates.Kernel.KGroupsE.K5126

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CertificateChecks.KernelKGroupsE

open CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.GH74.AS16.E2 CFSG.KS.PK

@[expose] def iterPk {n : Nat} (a : VP n) (k i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ acc => fd (wd n) a.1.1 acc) k

@[expose] def powOnePk {n : Nat} (k : Nat) (a : VP n) : Bool :=
  (List.range n).all fun i => iterPk a k i == i

@[expose] def commPk {n : Nat} (a b : VP n) : Bool :=
  (List.range n).all fun i =>
    fd (wd n) a.1.1 (fd (wd n) b.1.1 i) == fd (wd n) b.1.1 (fd (wd n) a.1.1 i)

@[expose] def eqPk {n : Nat} (a b : VP n) : Bool :=
  (List.range n).all fun i => fd (wd n) a.1.1 i == fd (wd n) b.1.1 i

@[expose] def c3Pk {n : Nat} (L : List (VP n)) (t : VP n) : List (VP n) :=
  L.filter fun c => powOnePk 3 c && commPk c t

@[expose] def local3Pk {n : Nat} (L : List (VP n)) (t : VP n) : Bool :=
  let cs := c3Pk L t
  (L.any fun y => eqPk y t) && !isOnePk t && powOnePk 2 t && cs.any (fun c => !isOnePk c) &&
    L.all fun a => bif cs.all (fun c => commPk a c) then (isOnePk a || eqPk a t) else true

@[expose] def expPk {n : Nat} (L : List (VP n)) (k m : Nat) : Bool :=
  L.all fun x => bif powOnePk k x then powOnePk m x else true

theorem iterPk_succ {n : Nat} (a : VP n) (k i : Nat) :
    iterPk a (k + 1) i = fd (wd n) a.1.1 (iterPk a k i) := rfl

theorem pkp_pow_apply {n : Nat} (a : VP n) (k : Nat) (i : Fin n) :
    (((pkp a) ^ k) i : Nat) = iterPk a k i := by
  induction k with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply]
    rfl
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, pkp_apply, ih, iterPk_succ]

theorem powOnePk_eq {n : Nat} (k : Nat) (a : VP n) : decide (pkp a ^ k = 1) = powOnePk k a := by
  refine decide_eq_of_iff ?_
  rw [perm_eq_iff_val, powOnePk, all_range_beq_iff]
  constructor
  · intro h i hi
    have e := h i hi hi
    rw [pkp_pow_apply, Equiv.Perm.one_apply] at e
    exact e
  · intro h i hi _
    rw [pkp_pow_apply, Equiv.Perm.one_apply]
    exact h i hi

theorem commPk_eq {n : Nat} (a b : VP n) :
    decide (pkp a * pkp b = pkp b * pkp a) = commPk a b := by
  refine decide_eq_of_iff ?_
  rw [perm_eq_iff_val, commPk, all_range_beq_iff]
  exact ⟨fun h i hi => h i hi hi, fun h i hi _ => h i hi⟩

theorem eqPk_eq {n : Nat} (a b : VP n) : decide (pkp a = pkp b) = eqPk a b := by
  refine decide_eq_of_iff ?_
  rw [perm_eq_iff_val, eqPk, all_range_beq_iff]
  exact ⟨fun h i hi => h i hi hi, fun h i hi _ => h i hi⟩

theorem isOnePk_eq' {n : Nat} (a : VP n) : decide (pkp a = 1) = isOnePk a :=
  decide_eq_of_iff (isOnePk_iff a).symm

theorem mem_map_pkp_eq {n : Nat} (L : List (VP n)) (t : VP n) :
    decide (pkp t ∈ L.map pkp) = L.any fun y => eqPk y t := by
  refine decide_eq_of_iff ?_
  rw [List.mem_map, List.any_eq_true]
  constructor
  · rintro ⟨y, hy, e⟩
    exact ⟨y, hy, by rw [← eqPk_eq]; exact decide_eq_true e⟩
  · rintro ⟨y, hy, e⟩
    rw [← eqPk_eq] at e
    exact ⟨y, hy, of_decide_eq_true e⟩

theorem local3Check_map_pkp {n : Nat} (L : List (VP n)) (t : VP n) :
    local3Check (L.map pkp) (pkp t) = local3Pk L t := by
  unfold local3Check c3list local3Pk c3Pk
  simp only [List.filter_map, List.all_map, List.any_map, Function.comp_def, powOnePk_eq,
    commPk_eq, isOnePk_eq, isOnePk_eq', eqPk_eq, mem_map_pkp_eq]

theorem expCheck_map_pkp {n : Nat} (L : List (VP n)) (k m : Nat) :
    expCheck (L.map pkp) k m = expPk L k m := by
  unfold expCheck expPk
  simp only [List.all_map, Function.comp_def, powOnePk_eq]

theorem m11_local3_5000K_pk :
    local3Pk (enumV (strongV M11.Q) M11.Q.base) (codeV M11.t0) = true := by
  decide +kernel

theorem m11_local3_5000K : local3Check (elemsV M11.Q) M11.t0 = true := by
  rw [elemsV, ← pkp_codeV M11.t0, local3Check_map_pkp]
  exact m11_local3_5000K_pk

theorem m11_exp_5000K_pk : expPk (enumV (strongV M11.Q) M11.Q.base) 27 3 = true := by
  decide +kernel

theorem m11_exp_5000K : expCheck (elemsV M11.Q) 27 3 = true := by
  rw [elemsV, expCheck_map_pkp]
  exact m11_exp_5000K_pk

theorem l33_local3_5000K_pk :
    local3Pk (enumV (strongV L33.QP) L33.QP.base) (codeV L33.t0) = true := by
  decide +kernel

theorem l33_local3_5000K : local3Check (elemsV L33.QP) L33.t0 = true := by
  rw [elemsV, ← pkp_codeV L33.t0, local3Check_map_pkp]
  exact l33_local3_5000K_pk

theorem l33_exp_5000K_pk : expPk (enumV (strongV L33.QP) L33.QP.base) 27 3 = true := by
  decide +kernel

theorem l33_exp_5000K : expCheck (elemsV L33.QP) 27 3 = true := by
  rw [elemsV, expCheck_map_pkp]
  exact l33_exp_5000K_pk

end CertificateChecks.KernelKGroupsE
