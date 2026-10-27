
module

public import Certificates.Kernel.Parrott946.Glue17b

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.Certificates.Kernel.PkCV
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups
  CertificateChecks.KernelA45 CFSG.Sporadic.SmallOddCore CFSG.KC.SylowReps CFSG.KC.ConjOrb Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def g3 (k : ℕ) : P45 := ((p3W.getD k []).map gA').prod

abbrev P3g : Subgroup P45 := closure (g3 '' {k | k < 3})

theorem prep_g3 : ∀ k < 3, PRep 45 6 (P3Z.G k) (g3 k) ∧ g3 k ∈ A :=
  fun _ hk => prep_word c17_binds.2.2.2.2.2.2.1 (by rw [c17_orders.2.2.2.2.2.2.1]; exact hk)

theorem P3g_le_A : P3g ≤ A := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (prep_g3 k hk).2

theorem p3_facts : Nat.card P3g = 81 ∧ ∀ y ∈ P3g, ∃ i < 81, PRep 45 6 (P3Z.T i) y :=
  group_A (fun k hk => (prep_g3 k hk).1) P3Z.cl P3Z.tr (by norm_num) c17_ids.2 P3Z.k

@[expose] def O3cls : Set P45 :=
  conjClass A sigma1 ∪ conjClass A (sigma1 * sigma2) ∪ conjClass A (sigma1 * sigma2⁻¹)

theorem cls_mem {N r : ℕ} {G GI T E D S : ℕ → ℕ} {s : P45}
    (hh : headK 45 6 3 G GI = true) (hg : ∀ k < 3, PRep 45 6 (G k) (gA' k))
    (hcl : ∀ i < N, closPt 45 6 3 N G GI T E i = true)
    (htr : ∀ i < N, treePt 3 N r E D i = true) (hr : r < N) (hs : PRep 45 6 (T r) s)
    (hK : distinctK N (fun i => pkeyK 45 6 ps (T i)) S = true) {p : ℕ} {x : P45}
    (hm : memK 45 6 ps N T S p = true) (hx : PRep 45 6 p x) : x ∈ conjClass A s := by
  obtain ⟨j, hj, e⟩ := memK_spec hm
  obtain ⟨g, hg', e2⟩ := (class_A hh hg hcl htr hr hs hK).2 j hj x (by rw [e]; exact hx)
  exact ⟨g, hg', e2⟩

theorem ord3K_of {p : ℕ} {x : P45} (hp : PRep 45 6 p x) (h3 : x * x * x = 1) (h1 : x ≠ 1) :
    ord3K p = true := by
  unfold ord3K
  rw [strictB_eq', bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, Ne,
    isIdK_iff (prep_pc hp (prep_pc hp hp)), isIdK_iff hp]
  exact ⟨by rw [← mul_assoc]; exact h3, h1⟩

theorem order_three_mem {x : P45} (hx : x ∈ A)
    (h3 : x * x * x = 1) (h1 : x ≠ 1) : x ∈ O3cls := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, bt1, bt12, bt12i, -⟩ := Parrott946.binds
  have hΦ : ∀ g ∈ A, ∀ y ∈ A, (fun z => z * z * z = 1 → z ≠ 1 → z ∈ O3cls) (g * y * g⁻¹) →
      (fun z => z * z * z = 1 → z ≠ 1 → z ∈ O3cls) y := by
    intro g hg y _ h hy3 hy1
    have hc3 : g * y * g⁻¹ * (g * y * g⁻¹) * (g * y * g⁻¹) = 1 := by
      calc g * y * g⁻¹ * (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y * y) * g⁻¹ := by group
        _ = 1 := by rw [hy3]; group
    have hc1 : g * y * g⁻¹ ≠ 1 := by
      intro h0
      apply hy1
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
    have hmem := h hc3 hc1
    have key : ∀ s : P45, g * y * g⁻¹ ∈ conjClass A s → y ∈ conjClass A s := by
      rintro s ⟨k, hk, e⟩
      refine ⟨g⁻¹ * k, A.mul_mem (A.inv_mem hg) hk, ?_⟩
      calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
        _ = g⁻¹ * k * s * (g⁻¹ * k)⁻¹ := by rw [e]; group
    rcases hmem with (hm | hm) | hm
    · exact Or.inl (Or.inl (key _ hm))
    · exact Or.inl (Or.inr (key _ hm))
    · exact Or.inr (key _ hm)
  have hT : ∀ y ∈ P3g, (fun z => z * z * z = 1 → z ≠ 1 → z ∈ O3cls) y := by
    intro y hy hy3 hy1
    obtain ⟨i, hi, hp⟩ := p3_facts.2 y hy
    have hc := allN_spec c17_p3 i hi
    rw [strictB_eq', Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
    rcases hc with ((hc | hc) | hc) | hc
    · rw [ord3K_of hp hy3 hy1] at hc
      exact absurd hc (by decide)
    · exact Or.inl (Or.inl (cls_mem (r := K1.r0) K1.h (prep_gens b0 b1 b2) K1.cl K1.tr0 (by decide)
        (by rw [← bt1]; exact prep_cOf _) K1.k hc hp))
    · exact Or.inl (Or.inr (cls_mem (r := K12.r0) K12.h (prep_gens b3 b4 b5) K12.cl K12.tr0 (by decide)
        (by rw [← bt12]; exact prep_cOf _) K12.k hc hp))
    · exact Or.inr (cls_mem (r := K12i.r0) K12i.h (prep_gens b6 b7 b8) K12i.cl K12i.tr0 (by decide)
        (by rw [← bt12i]; exact prep_cOf _) K12i.k hc hp)
  refine forall_of_sylow A P3g Nat.prime_three P3g_le_A (k := 4) (m := 640)
    (by rw [p3_facts.1]; norm_num) (by rw [card_A]; norm_num) (by decide) _ hΦ hT x hx ?_ h3 h1
  have e : x ^ 3 = 1 := by rw [pow_succ, sq, h3]
  have e81 : (3 : ℕ) ^ 4 = 3 * 27 := by norm_num
  rw [e81, pow_mul, e, one_pow]

theorem o3_conj {c x : P45} (hc : c ∈ A) (hx : x ∈ A) (h3 : x * x * x = 1) (h1 : x ≠ 1) :
    c * x * c⁻¹ ∈ A ∧ c * x * c⁻¹ * (c * x * c⁻¹) * (c * x * c⁻¹) = 1 ∧ c * x * c⁻¹ ≠ 1 := by
  refine ⟨A.mul_mem (A.mul_mem hc hx) (A.inv_mem hc), ?_, ?_⟩
  · calc c * x * c⁻¹ * (c * x * c⁻¹) * (c * x * c⁻¹) = c * (x * x * x) * c⁻¹ := by group
      _ = 1 := by rw [h3]; group
  · intro h
    apply h1
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group

theorem s1_ord3 : sigma1 * sigma1 * sigma1 = 1 ∧ sigma1 ≠ 1 := by
  refine ⟨?_, Alg.sigma1_ne_one⟩
  rw [← Alg.sigma1_cube, pow_succ, sq]

theorem s12_ord3 : sigma1 * sigma2 * (sigma1 * sigma2) * (sigma1 * sigma2) = 1 ∧
    sigma1 * sigma2 ≠ 1 := by
  constructor <;> decide +kernel

theorem s12i_ord3 : sigma1 * sigma2⁻¹ * (sigma1 * sigma2⁻¹) * (sigma1 * sigma2⁻¹) = 1 ∧
    sigma1 * sigma2⁻¹ ≠ 1 := by
  constructor <;> decide +kernel

theorem o3_set :
    {x : P45 | x ∈ A ∧ (x * x * x = 1 ∧ x ≠ 1)} = O3cls := by
  ext x
  constructor
  · rintro ⟨hx, h3, h1⟩
    exact order_three_mem hx h3 h1
  · rintro ((⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩) | ⟨c, hc, rfl⟩)
    · exact o3_conj hc sigma1_memA s1_ord3.1 s1_ord3.2
    · exact o3_conj hc (A.mul_mem sigma1_memA sigma2_memA) s12_ord3.1 s12_ord3.2
    · exact o3_conj hc (A.mul_mem sigma1_memA (A.inv_mem sigma2_memA)) s12i_ord3.1 s12i_ord3.2

theorem card_order_three : orderThreeCount () = 800 := by
  have c1 := card_cent_s1
  have c12 := card_cent_s12
  have c12i := card_cent_s12i
  have d12 : Disjoint (conjClass A sigma1) (conjClass A (sigma1 * sigma2)) :=
    class_disj (by rw [c1, c12]; norm_num)
  have d123 : Disjoint (conjClass A sigma1 ∪ conjClass A (sigma1 * sigma2))
      (conjClass A (sigma1 * sigma2⁻¹)) :=
    Set.disjoint_union_left.2 ⟨class_disj (by rw [c1, c12i]; norm_num),
      class_disj (by rw [c12, c12i]; norm_num)⟩
  unfold orderThreeCount
  rw [← card_filter QA45 QA45_ok (p := fun g : P45 => g * g * g = 1 ∧ g ≠ 1),
    card_sub_ncard (fun g : P45 => g * g * g = 1 ∧ g ≠ 1), o3_set, O3cls, Set.ncard_union_eq d123, Set.ncard_union_eq d12,
    class_ncard c1 (by norm_num), class_ncard c12 (by norm_num), class_ncard c12i (by norm_num)]

end CertificateChecks.Parrott946

end
