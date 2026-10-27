module

public import Certificates.Kernel.Multipliers.Quot
public import CFSG.Certificates.Kernel.Multipliers.MonoSound

public section

namespace CertificateChecks.KernelTwoCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Certificates.CosetEnumeration

variable {m : ℕ}

@[expose] noncomputable def zk (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool))
    (k : ℕ) : PG m (coverWords R w) :=
  PresentedGroup.mk _ (FreeGroup.mk (R.getD k []))

theorem mem_comm (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool)) (i : Fin m)
    {k : ℕ} (hk : k < R.length) : commWord [(i, true)] (R.getD k []) ∈ coverWords R w := by
  unfold coverWords
  refine List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange i, ?_⟩)
  exact List.mem_map_of_mem (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)

theorem cover_mem (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool)) (i : Fin m) :
    (i, false) :: w i ∈ coverWords R w := by
  unfold coverWords
  exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange i))

theorem zk_central (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool)) {k : ℕ}
    (hk : k < R.length) : zk R w k ∈ Subgroup.center (PG m (coverWords R w)) := by
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← PresentedGroup.closure_range_of,
    Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨i, rfl⟩
  have h : PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ (coverWords R w).map FreeGroup.mk}
      (FreeGroup.mk (commWord [(i, true)] (R.getD k []))) = 1 :=
    PresentedGroup.one_of_mem (List.mem_map_of_mem (mem_comm R w i hk))
  rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem card_le_two_mul (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool))
    [Finite (PG m R)] {z : PG m (coverWords R w)} (hz : z ∈ Subgroup.center _) (hz2 : z ^ 2 = 1)
    (hR : ∀ k < R.length, zk R w k ∈ Subgroup.zpowers z) :
    Finite (PG m (coverWords R w)) ∧ Nat.card (PG m (coverWords R w)) ≤ Nat.card (PG m R) * 2 := by
  have : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hz)
  have hfo : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by norm_num, hz2⟩
  have : Finite (Subgroup.zpowers z) := finite_zpowers.mpr hfo
  obtain ⟨f, c⟩ := CertificateChecks.KernelMult.card_le_mul_of_relators R (coverWords R w)
    (Subgroup.zpowers z) (fun r hr => by
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hr
      have := hR k hk
      simpa only [zk, List.getD_eq_getElem _ _ hk] using this)
  have h2 : Nat.card (Subgroup.zpowers z) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) hz2
  exact ⟨f, c.trans (Nat.mul_le_mul_left _ h2)⟩

theorem two_dvd_orderOf_of_mono {N : ℕ} (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) {Rc Wc : List (List ℕ)} (hR : codes R = Rc)
    (hW : codes ((List.finRange m).map fun i => (i, false) :: w i) = Wc) {T C : ℕ → ℕ}
    (hp : CFSG.KC.Mono.paramsOK N 2 C R.length = true)
    (h : ∀ x < N, CFSG.KC.Mono.pointOK T m N 2 C Rc Wc x = true) {k : ℕ} (hk : k < R.length)
    (hC : C k = 1) : 2 ∣ orderOf (zk R w k) := by
  obtain ⟨E, _, ψ, τ, hτ, hψ⟩ := CFSG.Certificates.Mono.mono_sound R w hR hW hp h
  have e : ψ (zk R w k) = τ (Multiplicative.ofAdd (1 : ZMod 2)) := by
    rw [zk, List.getD_eq_getElem _ _ hk, hψ k hk, hC, Nat.cast_one]
  have h1 : orderOf (ψ (zk R w k)) = 2 := by
    rw [e, orderOf_injective τ hτ, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  rw [← h1]
  exact orderOf_map_dvd ψ _

noncomputable def mulEquivOfIsPresentation {X : Type*} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R)) : PG m R ≃* X :=
  (QuotientGroup.quotientMulEquivOfEq hP.ker_lift.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hP.lift_surjective)

theorem card_PG_eq_of_isPresentation {X : Type*} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R)) :
    Nat.card (PG m R) = Nat.card X :=
  Nat.card_congr (mulEquivOfIsPresentation hP).toEquiv

end CertificateChecks.KernelTwoCover

end
