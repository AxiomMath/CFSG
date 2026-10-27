
module

public import Certificates.Kernel.Parrott946.Glue17a
public import Certificates.Kernel.Parrott946.Glue16

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups
  CertificateChecks.KernelA45 CFSG.Sporadic.SmallOddCore CFSG.KC.SylowReps Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem prep_ut : PRep 45 6 (pc (wE 1) (wE 0)) (u * t) := prep_pc prep_u prep_t
theorem prep_uv : PRep 45 6 (pc (wE 1) (wE 2)) (u * v) := prep_pc prep_u prep_v

theorem ut_memA : u * t ∈ A := A.mul_mem u_memA t_memA
theorem uv_memA : u * v ∈ A := A.mul_mem u_memA v_memA

theorem ut_inv : u * t * (u * t) = 1 ∧ u * t ≠ 1 := (inv_iff_isInvK prep_ut).1 c17_fix.1
theorem uv_inv : u * v * (u * v) = 1 ∧ u * v ≠ 1 := (inv_iff_isInvK prep_uv).1 c17_fix.2.1

theorem fixC_ut : fixC (u * t) = 5 := by rw [← fixK_eq prep_ut]; exact c17_fix.2.2.1
theorem fixC_uv : fixC (u * v) = 15 := by rw [← fixK_eq prep_uv]; exact c17_fix.2.2.2

theorem card_cent_ut :
    Nat.card ↥(A ⊓ centralizer ({u * t} : Set P45)) = 192 := by
  rw [card_cent_eq ut_memA ut_inv.1 ut_inv.2, fixC_ut]
  rfl

theorem card_cent_uv :
    Nat.card ↥(A ⊓ centralizer ({u * v} : Set P45)) = 1440 := by
  rw [card_cent_eq uv_memA uv_inv.1 uv_inv.2, fixC_uv]
  rfl

theorem centralizer_ut : commCount (u * t) = 192 := by
  rw [commCount_eq, filter_cent, card_cent_ut]

theorem centralizer_uv : commCount (u * v) = 1440 := by
  rw [commCount_eq, filter_cent, card_cent_uv]

theorem class_card_cent {r x : P45} (hx : x ∈ conjClass A r) :
    Nat.card ↥(A ⊓ centralizer ({x} : Set P45)) = Nat.card ↥(A ⊓ centralizer ({r} : Set P45)) := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact card_cent_conj hc

theorem class_ncard {r : P45} {c : ℕ}
    (hc : Nat.card ↥(A ⊓ centralizer ({r} : Set P45)) = c) (hc0 : 0 < c) :
    (conjClass A r).ncard = 51840 / c := by
  have h := ncard_conjClass_mul_card A r
  rw [card_A] at h
  change _ * Nat.card ↥(A ⊓ centralizer ({r} : Set P45)) = _ at h
  rw [hc] at h
  rw [← h, Nat.mul_div_cancel _ hc0]

theorem class_disj {r s : P45}
    (h : Nat.card ↥(A ⊓ centralizer ({r} : Set P45)) ≠ Nat.card ↥(A ⊓ centralizer ({s} : Set P45))) :
    Disjoint (conjClass A r) (conjClass A s) :=
  Set.disjoint_left.2 fun _ hx hy => h ((class_card_cent hx).symm.trans (class_card_cent hy))

theorem card_sub_ncard (p : P45 → Prop) :
    Nat.card {g : A // p g} = {x : P45 | x ∈ A ∧ p x}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mem_class_of {r x : P45} {c : P45} (hc : c ∈ A) (e : x = c * r * c⁻¹) :
    x ∈ conjClass A r := ⟨c, hc, e⟩

theorem rep_eq_of_fix {r r' : P45}
    (hr : r ∈ [Certificates.P43Twin.tA (), Certificates.P43Twin.tB (), Certificates.P43Twin.t36 (),
      Certificates.P43Twin.t540 ()])
    (hr' : r' ∈ [Certificates.P43Twin.tA (), Certificates.P43Twin.tB (), Certificates.P43Twin.t36 (),
      Certificates.P43Twin.t540 ()]) (h : fixC r = fixC r') : r = r' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
  rcases hr with rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;>
    first
    | (rw [fix_tA, fix_tB] at h; omega) | (rw [fix_tA, fix_t36] at h; omega)
    | (rw [fix_tA, fix_t540] at h; omega) | (rw [fix_tB, fix_tA] at h; omega)
    | (rw [fix_tB, fix_t36] at h; omega) | (rw [fix_tB, fix_t540] at h; omega)
    | (rw [fix_t36, fix_tA] at h; omega) | (rw [fix_t36, fix_tB] at h; omega)
    | (rw [fix_t36, fix_t540] at h; omega) | (rw [fix_t540, fix_tA] at h; omega)
    | (rw [fix_t540, fix_tB] at h; omega) | (rw [fix_t540, fix_t36] at h; omega) | rfl

theorem conj_of_fix {x y : P45} (hx : x ∈ A) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) (hy : y ∈ A) (hy2 : y * y = 1) (hy1 : y ≠ 1) (h : fixC x = fixC y) :
    ∃ c ∈ A, x = c * y * c⁻¹ := by
  obtain ⟨r, hr, g, hg, e⟩ := inCls_of_inv hx hx2 hx1
  obtain ⟨r', hr', g', hg', e'⟩ := inCls_of_inv hy hy2 hy1
  have hrr : r = r' := rep_eq_of_fix hr hr' (by rw [← fixC_conj r g, ← e, h, e', fixC_conj])
  subst hrr
  refine ⟨g * g'⁻¹, A.mul_mem hg (A.inv_mem hg'), ?_⟩
  rw [e, e']
  group

theorem fix_cases {x : P45} (hx : x ∈ A) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) : fixC x = 13 ∨ fixC x = 5 ∨ fixC x = 15 ∨ fixC x = 7 := by
  obtain ⟨r, hr, g, hg, e⟩ := inCls_of_inv hx hx2 hx1
  rw [e, fixC_conj]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Or.inl fix_tA
  · exact Or.inr (Or.inl fix_tB)
  · exact Or.inr (Or.inr (Or.inl fix_t36))
  · exact Or.inr (Or.inr (Or.inr fix_t540))

theorem conj_inv {c x : P45} (hc : c ∈ A) (hx : x ∈ A) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    c * x * c⁻¹ ∈ A ∧ c * x * c⁻¹ * (c * x * c⁻¹) = 1 ∧ c * x * c⁻¹ ≠ 1 := by
  refine ⟨A.mul_mem (A.mul_mem hc hx) (A.inv_mem hc), ?_, ?_⟩
  · calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  · intro h
    apply hx1
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group

theorem inv_set :
    {x : P45 | x ∈ A ∧ (x * x = 1 ∧ x ≠ 1)} =
      conjClass A t ∪ conjClass A (u * t) ∪ conjClass A (u * v) ∪ conjClass A v := by
  ext x
  constructor
  · rintro ⟨hx, hx2, hx1⟩
    rcases fix_cases hx hx2 hx1 with h | h | h | h
    · obtain ⟨c, hc, e⟩ := conj_of_fix hx hx2 hx1 t_memA Alg.t_sq Alg.t_ne_one (by rw [h, fixC_t])
      exact Or.inl (Or.inl (Or.inl (mem_class_of hc e)))
    · obtain ⟨c, hc, e⟩ := conj_of_fix hx hx2 hx1 ut_memA ut_inv.1 ut_inv.2 (by rw [h, fixC_ut])
      exact Or.inl (Or.inl (Or.inr (mem_class_of hc e)))
    · obtain ⟨c, hc, e⟩ := conj_of_fix hx hx2 hx1 uv_memA uv_inv.1 uv_inv.2 (by rw [h, fixC_uv])
      exact Or.inl (Or.inr (mem_class_of hc e))
    · obtain ⟨c, hc, e⟩ := conj_of_fix hx hx2 hx1 v_memA Alg.v_sq Alg.v_ne_one (by rw [h, fixC_v])
      exact Or.inr (mem_class_of hc e)
  · rintro (((⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩)
    · exact conj_inv hc t_memA Alg.t_sq Alg.t_ne_one
    · exact conj_inv hc ut_memA ut_inv.1 ut_inv.2
    · exact conj_inv hc uv_memA uv_inv.1 uv_inv.2
    · exact conj_inv hc v_memA Alg.v_sq Alg.v_ne_one

theorem card_involutions : involutionCount () = 891 := by
  have ct := card_cent_t Alg.t_sq Alg.t_ne_one
  have cv := card_cent_v Alg.v_sq Alg.v_ne_one
  have cut := card_cent_ut
  have cuv := card_cent_uv
  have d12 : Disjoint (conjClass A t) (conjClass A (u * t)) :=
    class_disj (by rw [ct, cut]; norm_num)
  have d123 : Disjoint (conjClass A t ∪ conjClass A (u * t)) (conjClass A (u * v)) :=
    Set.disjoint_union_left.2 ⟨class_disj (by rw [ct, cuv]; norm_num),
      class_disj (by rw [cut, cuv]; norm_num)⟩
  have d1234 : Disjoint (conjClass A t ∪ conjClass A (u * t) ∪ conjClass A (u * v))
      (conjClass A v) :=
    Set.disjoint_union_left.2 ⟨Set.disjoint_union_left.2 ⟨class_disj (by rw [ct, cv]; norm_num),
      class_disj (by rw [cut, cv]; norm_num)⟩, class_disj (by rw [cuv, cv]; norm_num)⟩
  unfold involutionCount
  rw [← card_filter QA45 QA45_ok (p := fun g : P45 => g * g = 1 ∧ g ≠ 1),
    card_sub_ncard (fun g : P45 => g * g = 1 ∧ g ≠ 1), inv_set, Set.ncard_union_eq d1234, Set.ncard_union_eq d123, Set.ncard_union_eq d12,
    class_ncard ct (by norm_num), class_ncard cut (by norm_num), class_ncard cuv (by norm_num),
    class_ncard cv (by norm_num)]

end CertificateChecks.Parrott946

end
