module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22E8Data
import Certificates.Kernel.SmallSpor.M22Glue
import Certificates.Kernel.SmallSpor.M22E8Checks
import CFSG.Certificates.Kernel.ListBridge.CommSound

namespace CertificateChecks.KernelSmallSpor.M22

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ClassicalInvolution
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.ListBridge
open CFSG.ClassicalInvolution.ListBridge
open scoped commutatorElement

theorem ngK3 : EK.ng = 3 := Nat.eq_of_beq_eq_true nums.1

theorem ngU3 : EU.ng = 3 := Nat.eq_of_beq_eq_true nums.2

theorem lenE : m22E8CommGens.length = EE.ng := by
  rw [Nat.eq_of_beq_eq_true numE.2.1]
  rfl

theorem prepE : ∀ j < EE.ng, PRep 22 5 (EE.G j) (m22E8CommGens.getD j 1) := by
  intro j hj
  have hj3 : j < 3 := by rwa [← Nat.eq_of_beq_eq_true numE.2.1]
  have h32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have hw : (22 : Nat) < 2 ^ 5 := by norm_num
  have p0 := prepU 0 (by rw [ngU3]; norm_num)
  have p1 := prepU 1 (by rw [ngU3]; norm_num)
  have p2 := prepU 2 (by rw [ngU3]; norm_num)
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true bindE0]
    exact prep_pcommutK h32 hw p0 p1
  · rw [Nat.eq_of_beq_eq_true bindE1]
    exact prep_pcommutK h32 hw p0 p2
  · rw [Nat.eq_of_beq_eq_true bindE2]
    exact prep_pcommutK h32 hw p1 p2

theorem mem_E (x : Equiv.Perm (Fin 22)) :
    x ∈ m22E8EL ↔ x ∈ Subgroup.closure {s | s ∈ m22E8CommGens} :=
  mem_permClosureList_iff _ 20 (by
    rw [(enum_closure EE.ok lenE prepE).2, Nat.eq_of_beq_eq_true numE.2.2]
    norm_num) x

theorem commGens_le : Subgroup.closure {s | s ∈ m22E8CommGens} ≤
    Subgroup.closure {s | s ∈ m22UGens1} := by
  set U := Subgroup.closure {s | s ∈ m22UGens1}
  have hc : ∀ a ∈ U, ∀ b ∈ U, ⁅a, b⁆ ∈ U := fun a ha b hb => by
    rw [commutatorElement_def]
    exact U.mul_mem (U.mul_mem (U.mul_mem ha hb) (U.inv_mem ha)) (U.inv_mem hb)
  have hg : ∀ j < 3, m22UGens1.getD j 1 ∈ U := fun j hj =>
    Subgroup.subset_closure (getD_mem (by rw [lenU, ngU3]; exact hj))
  refine (Subgroup.closure_le U).2 fun c hc' => ?_
  simp only [Set.mem_setOf_eq, m22E8CommGens, List.mem_cons, List.not_mem_nil, or_false] at hc'
  rcases hc' with rfl | rfl | rfl
  · exact hc _ (hg 0 (by norm_num)) _ (hg 1 (by norm_num))
  · exact hc _ (hg 0 (by norm_num)) _ (hg 2 (by norm_num))
  · exact hc _ (hg 1 (by norm_num)) _ (hg 2 (by norm_num))

theorem facts9316 : M22E8Facts := by
  have h32 : (22 : Nat) < 2 ^ 32 := by norm_num
  have hw : (22 : Nat) < 2 ^ 5 := by norm_num
  have eU := enum_closure EU.ok lenU prepU
  have eE := enum_closure EE.ok lenE prepE
  have hUg : ∀ g ∈ m22UGens1, g ∈ m22E8UL := fun g hg =>
    (mem_U g).2 (Subgroup.subset_closure hg)
  have hUj : ∀ j < 3, m22UGens1.getD j 1 ∈ m22E8UL := fun j hj =>
    hUg _ (getD_mem (by rw [lenU, ngU3]; exact hj))
  have hKj : ∀ j < 3, m22KGens1.getD j 1 ∈ m22E8KL := fun j hj =>
    (mem_K _).2 (Subgroup.subset_closure (getD_mem (by rw [lenK, ngK3]; exact hj)))
  have hEU : ∀ x ∈ m22E8EL, x ∈ m22E8UL := fun x hx => (mem_U x).2 (commGens_le ((mem_E x).1 hx))
  refine ⟨?_, permClosureList_nodup _ _, hUg, hUj 0 (by norm_num), hUj 1 (by norm_num),
    hUj 2 (by norm_num), hKj 0 (by norm_num), hKj 1 (by norm_num), ?_, ?_,
    permClosureList_nodup _ _, (mem_E 1).2 (Subgroup.one_mem _),
    fun x hx y hy => (mem_E _).2 (Subgroup.mul_mem _ ((mem_E x).1 hx) ((mem_E y).1 hy)),
    fun x hx => (mem_E _).2 (Subgroup.inv_mem _ ((mem_E x).1 hx)),
    fun x hx => sq_of_K EE.ok lenE prepE powE x ((mem_E x).1 hx),
    fun x hx y hy => abel_of_K EE.ok lenE prepE abelE x ((mem_E x).1 hx) y ((mem_E y).1 hy),
    hEU, fun x hx => (mem_E x).2 (Subgroup.subset_closure hx),
    fun x hx y hy => (mem_E _).2 (comm_mem_of_K EU.ok lenU prepU EE.ok lenE prepE commU x
      ((mem_U x).1 hx) y ((mem_U y).1 hy))⟩
  · have h := length_eq_card _ mem_U (permClosureList_nodup m22UGens1 20)
    rw [eU.2, Nat.eq_of_beq_eq_true numE.1] at h
    exact h
  · intro h
    exact not_mem_of_K EU.ok lenU prepU
      (prep_pcommutK h32 hw (prepK 0 (by rw [ngK3]; norm_num)) (prepK 1 (by rw [ngK3]; norm_num)))
      xyCanon xyOut ((mem_U _).1 h)
  · have h := length_eq_card _ mem_E (permClosureList_nodup m22E8CommGens 20)
    rw [eE.2, Nat.eq_of_beq_eq_true numE.2.2] at h
    exact h

public theorem check9316 : m22E8Check = true := by
  have f := facts9316
  simp only [m22E8Check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]
  exact ⟨f.ul_length, f.ul_nodup, f.ugens_mem, f.u0_mem, f.u1_mem, f.u2_mem, f.x_mem, f.y_mem,
    f.xy_not_mem, f.el_length, f.el_nodup, f.el_one, f.el_mul, f.el_inv, f.el_sq, f.el_comm,
    f.el_le_ul, f.commgens_mem, f.ul_comm_mem⟩

end CertificateChecks.KernelSmallSpor.M22
