
module

public import Certificates.Kernel.PermCent.KG5124GlueBase

public import Certificates.Kernel.PermCent.KG5123B
public import CFSG.GH74.KGroups.L34Aut

public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5124

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.GLS.Stage1.Thm6.Sec13

theorem x0_mem' : x0 ∈ QP.originalSubgroup := mem_of_siftC QP QP_ok x0 kX0.1

theorem conj_PA (y : Equiv.Perm (Fin 42)) (hy : y ∈ QP.originalSubgroup) (h2 : orderOf y = 2) :
    ∃ g ∈ QP.originalSubgroup, g * PA * g⁻¹ = y := by
  have hmem : cOf y ∈ (elemsC QP).filter fun x => orderIsC x 2 := by
    rw [List.mem_filter, mem_elemsC QP QP_ok, ev_cOf, ← orderIs_C, ev_cOf,
      orderIs_iff y (by norm_num)]
    exact ⟨hy, by simpa using h2⟩
  obtain ⟨g, hg, hc⟩ := List.any_eq_true.1 (List.all_eq_true.1 K5123.kConj _ hmem)
  rw [eq22C_eq, decide_eq_true_iff] at hc
  have := congrArg ev hc
  rw [← ev_mul', ← ev_mul', ev_cOf, ev_cOf] at this
  refine ⟨ev g, (mem_elemsC QP QP_ok g).1 hg, ?_⟩
  rw [this, mul_inv_cancel_right]

theorem cls_P : cls QP.originalSubgroup x0 = {y | y ∈ QP.originalSubgroup ∧ orderOf y = 2} := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨QP.originalSubgroup.mul_mem (QP.originalSubgroup.mul_mem hm x0_mem')
      (QP.originalSubgroup.inv_mem hm), ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact x0_order
  · rintro ⟨hy, h2⟩
    obtain ⟨g, hg, rfl⟩ := conj_PA y hy h2
    obtain ⟨h, hh, hx⟩ := conj_PA x0 x0_mem' x0_order
    refine ⟨g * h⁻¹, QP.originalSubgroup.mul_mem hg (QP.originalSubgroup.inv_mem hh), ?_⟩
    rw [← hx]
    group

theorem card_invol : Nat.card {y | y ∈ QP.originalSubgroup ∧ orderOf y = 2} = 315 := by
  have h := card_eq_length
    (fun y : Equiv.Perm (Fin 42) => y ∈ QP.originalSubgroup ∧ orderOf y = 2) cOf
    (fun a b e => by simpa [ev_cOf] using congrArg ev e) ((elemsC QP).filter fun x => orderIsC x 2)
    ((nodup_elemsC QP QP_ok).filter _) (fun b => by
      rw [List.mem_filter, mem_elemsC QP QP_ok, ← orderIs_C, orderIs_iff _ (by norm_num)]
      exact ⟨fun h => ⟨ev b, h, cOf_ev' b⟩, fun ⟨a, ha, e⟩ => by rw [← e, ev_cOf]; exact ha⟩)
  rw [K5123.kInv] at h
  exact h

theorem conj_mem_P (σ : Equiv.Perm (Fin 42)) (hσ : σ ∈ QA.originalSubgroup)
    (y : Equiv.Perm (Fin 42)) (hy : y ∈ QP.originalSubgroup) : σ * y * σ⁻¹ ∈ QP.originalSubgroup := by
  have hnorm : QA.originalSubgroup ≤
      Subgroup.normalizer (QP.originalSubgroup : Set (Equiv.Perm (Fin 42))) := by
    have e : QA.originalSubgroup = Subgroup.closure {g | g ∈ QA.original.toList} := rfl
    rw [e, Subgroup.closure_le]
    intro τ hτ
    have h1 := List.all_eq_true.1 norm_ok τ hτ
    simp only [Bool.and_eq_true] at h1
    have ha : τ * PA * τ⁻¹ ∈ QP.originalSubgroup := (mem_iff_sift QP QP_ok _).2 h1.1
    have hb : τ * PB * τ⁻¹ ∈ QP.originalSubgroup := (mem_iff_sift QP QP_ok _).2 h1.2
    have hle : Subgroup.closure ({PA, PB} : Set (Equiv.Perm (Fin 42))) ≤
        QP.originalSubgroup.comap (MulAut.conj τ).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
    refine mem_normalizer_of_conj_mem QP.originalSubgroup τ fun z hz => ?_
    rw [QP_closure] at hz
    exact hle hz
  exact (Subgroup.mem_normalizer_iff.1 (hnorm hσ) y).1 hy

theorem cls_A : cls QA.originalSubgroup x0 = cls QP.originalSubgroup x0 := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [cls_P]
    refine ⟨conj_mem_P m hm x0 x0_mem', ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact x0_order
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, P_le_A' hm, rfl⟩

theorem card_CP' : Nat.card ↥(QP.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) = 64 := by
  have h := card_cls_mul QP.originalSubgroup x0_mem'
  rw [cls_P, card_invol, card_group QP QP_ok, QP_valid.2] at h
  omega

theorem card_CA' : Nat.card ↥(QA.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42)))) = 768 := by
  have h := card_cls_mul QA.originalSubgroup (P_le_A' x0_mem')
  rw [cls_A, cls_P, card_invol, card_group QA QA_ok, QA_valid.2] at h
  omega

theorem QH_eq : QH.originalSubgroup =
    QA.originalSubgroup ⊓ Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42))) := by
  have hle : QH.originalSubgroup ≤
      QA.originalSubgroup ⊓ Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42))) := by
    rw [QH, certificate_originalSubgroup, Subgroup.closure_le]
    intro g hg
    have h := List.all_eq_true.1 kHGens g hg
    rw [Bool.and_eq_true] at h
    exact Subgroup.mem_inf.2 ⟨mem_of_siftC QA QA_ok g h.1,
      Subgroup.mem_centralizer_singleton_iff.2 (comm_of_eq22C h.2)⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_CA', card_group QH QH_ok, orderCertificate_eq_orderV, kQH.2]

theorem cent_sq' : ∀ σ ∈ QA.originalSubgroup, (∀ q ∈ QP.originalSubgroup ⊓
    Subgroup.centralizer ({x0} : Set (Equiv.Perm (Fin 42))), σ * q = q * σ) → σ ^ 2 = 1 := by
  intro σ hσ hc
  have hx : σ * x0 = x0 * σ :=
    hc x0 (Subgroup.mem_inf.2 ⟨x0_mem', Subgroup.mem_centralizer_singleton_iff.2 rfl⟩)
  have hH : σ ∈ QH.originalSubgroup := by
    rw [QH_eq]
    exact Subgroup.mem_inf.2 ⟨hσ, Subgroup.mem_centralizer_singleton_iff.2 hx⟩
  have h1 := List.all_eq_true.1 kSq (cOf σ) ((mem_elemsC QH QH_ok _).2 (by rw [ev_cOf]; exact hH))
  have hk : (kGens.all fun k => eq22C (cOf σ) (cOf k) (cOf k) (cOf σ)) = true := by
    rw [List.all_eq_true]
    intro k hk
    have h := List.all_eq_true.1 kKGens k hk
    rw [Bool.and_eq_true] at h
    have hq := hc k (Subgroup.mem_inf.2 ⟨mem_of_siftC QP QP_ok k h.1,
      Subgroup.mem_centralizer_singleton_iff.2 (comm_of_eq22C h.2)⟩)
    rw [eq22C_eq, decide_eq_true_iff, ← ev_eq_iff, ← ev_mul', ← ev_mul', ev_cOf, ev_cOf]
    exact hq
  beta_reduce at h1
  rw [hk, Bool.not_true, Bool.false_or, powOneC_eq, decide_eq_true_iff] at h1
  have := congrArg ev h1
  rwa [← ev_pow', ev_cOf, ev_one] at this

theorem one_class' : ∀ y ∈ QP.originalSubgroup, y ^ 2 = 1 → y ≠ 1 →
    ∃ g ∈ QP.originalSubgroup, g * x0 * g⁻¹ = y := by
  intro y hy h2 h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy' : y ∈ cls QP.originalSubgroup x0 := by
    rw [cls_P]
    exact ⟨hy, orderOf_eq_prime_iff.2 ⟨h2, h1⟩⟩
  obtain ⟨g, hg, e⟩ := hy'
  exact ⟨g, hg, e.symm⟩

theorem x0_facts : x0 ^ 2 = 1 ∧ x0 ≠ 1 ∧ x0 ∈ QP.originalSubgroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2⟩ := orderOf_eq_prime_iff.1 x0_order
  exact ⟨h1, h2, x0_mem'⟩

end CFSG.Certificates.Kernel.PkCV.KGrp.K5124
