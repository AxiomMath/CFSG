module

public import Certificates.Kernel.Misc.GL4.S3K
public import Certificates.Kernel.Misc.GL4.S3Small
public import Certificates.Kernel.Misc.GL4.A5Facts
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.GL4S3

open Matrix CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4 Certificates.A5GL42 Certificates.S3x3GL42
open Certificates.GL4 (GL4)
open CertificateChecks.KernelMisc.GL4EA (EA ea_exact)
open CertificateChecks.KernelMisc.GL4A5 (subspaces_complete subspace_eq stab_of vecOfCode_zero
  det_eq_one subC)

theorem commB_iff (x y : ℕ) : commB x y = true ↔ ofCode x * ofCode y = ofCode y * ofCode x := by
  unfold commB
  constructor
  · intro h
    have := congrArg ofCode (beq_iff.1 h)
    rwa [mul4F_ofCode, mul4F_ofCode] at this
  · intro h
    exact beq_iff.2 (ofCode_inj (mul4F_lt _ _) (mul4F_lt _ _) (by rw [mul4F_ofCode, mul4F_ofCode, h]))

theorem mulEq_iff (x y z w : ℕ) :
    Nat.beq (mul4F x y) (mul4F z w) = true ↔ ofCode x * ofCode y = ofCode z * ofCode w := by
  constructor
  · intro h
    have := congrArg ofCode (beq_iff.1 h)
    rwa [mul4F_ofCode, mul4F_ofCode] at this
  · intro h
    exact beq_iff.2 (ofCode_inj (mul4F_lt _ _) (mul4F_lt _ _) (by rw [mul4F_ofCode, mul4F_ofCode, h]))

theorem one_iff {x : ℕ} (hx : x < 65536) : Nat.beq x id4 = true ↔ ofCode x = 1 :=
  beq_iff.trans (ofCode_eq_one hx).symm

theorem sq_iff (x : ℕ) : Nat.beq (mul4F x x) id4 = true ↔ ofCode x * ofCode x = 1 := by
  rw [one_iff (mul4F_lt _ _), mul4F_ofCode]

theorem o3_iff {x : ℕ} (hx : x < 65536) :
    o3B x (mul4F x x) = true ↔ ofCode x * ofCode x * ofCode x = 1 ∧ ofCode x ≠ 1 := by
  unfold o3B
  rw [andB_iff, notB_iff, one_iff (mul4F_lt _ _), one_iff hx, mul4F_ofCode, mul4F_ofCode]

theorem s3_ok (k : ℕ) (hk : k < 20160) : s3At k = true := by
  have h := S3K.all (k / 5040) (Nat.lt_of_lt_of_le (by omega : k / 5040 < 4) (by decide))
  exact (CFSG.KC.Misc.Clos.allR_iff _ _ _).1 h k (Nat.mul_div_le k 5040) (by
    change k < 5040 * (k / 5040) + 5040
    omega)

theorem idx (g : GL4) : ∃ k < 20160, enc4 g = EA k := ea_exact.2.1 g (Subgroup.mem_top _)

theorem wW_spec {x w : ℕ} (h : wW x w = true) : ∃ j t, j < 20160 ∧ t < 2 ∧
    ofCode (EA j) * ofCode x = ofCode (sA0 t) * ofCode (EA j) := by
  unfold wW at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨hj, h⟩ := andB_iff.1 h
  obtain ⟨ht, h⟩ := andB_iff.1 h
  exact ⟨_, _, Nat.blt_eq.mp hj, Nat.blt_eq.mp ht, (mulEq_iff _ _ _ _).1 h⟩

theorem vW_spec {t x h : ℕ} (hv : vW t x h = true) : h < 20160 ∧
    ofCode (EA h) * ofCode (sA0 t) = ofCode (sA0 t) * ofCode (EA h) ∧
    ofCode (EA h) * ofCode x = ofCode (sB0 t) * ofCode (EA h) := by
  unfold vW at hv
  obtain ⟨hh, hv⟩ := andB_iff.1 hv
  obtain ⟨h1, h2⟩ := andB_iff.1 hv
  exact ⟨Nat.blt_eq.mp hh, (commB_iff _ _).1 h1, (mulEq_iff _ _ _ _).1 h2⟩

theorem facts_at (g : GL4) :
    (o3B (enc4 g) (mul4F (enc4 g) (enc4 g)) = true → ∃ k, wW (enc4 g) k = true) ∧
    ∀ t < 2,
      (o3B (enc4 g) (mul4F (enc4 g) (enc4 g)) = true → commB (enc4 g) (sA0 t) = true →
        (∃ w, vW t (enc4 g) w = true) ∨ inL (bd t) (bN t) (enc4 g) = true) ∧
      (Nat.beq (mul4F (enc4 g) (enc4 g)) id4 = true →
        Nat.beq (mul4F (enc4 g) (sA0 t)) (mul4F (mul4F (sA0 t) (sA0 t)) (enc4 g)) = true →
        (∀ i < bN t, notB (commB (enc4 g) (bd t i)) = true) ∧
          (commB (enc4 g) (sB0 t) = true → inL (cL t) 3 (enc4 g) = true)) ∧
      (commB (enc4 g) (sA0 t) = true → ∀ i < 3, commB (enc4 g) (cL t i) = true →
        inL (cT t i) 6 (enc4 g) = true) := by
  obtain ⟨k, hk, hkc⟩ := idx g
  have h := s3_ok k hk
  unfold s3At at h
  rw [letB_eq, letB_eq, ← hkc] at h
  obtain ⟨hA, hT⟩ := andB_iff.1 h
  refine ⟨fun ho => ⟨_, impB_iff.1 hA ho⟩, fun t ht => ?_⟩
  have h2 := (allN_iff _ _).1 hT t ht
  unfold tAt at h2
  rw [letB_eq] at h2
  obtain ⟨hB, h2⟩ := andB_iff.1 h2
  obtain ⟨hC, hD⟩ := andB_iff.1 h2
  refine ⟨fun ho hc => ?_, fun h1 h2 => ?_, fun hc i hi hci => ?_⟩
  · rcases orB_iff.1 (impB_iff.1 hB (andB_iff.2 ⟨ho, hc⟩)) with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  · obtain ⟨h3, h4⟩ := andB_iff.1 (impB_iff.1 hC (andB_iff.2 ⟨h1, h2⟩))
    exact ⟨(allN_iff _ _).1 h3, impB_iff.1 h4⟩
  · exact impB_iff.1 ((allN_iff _ _).1 (impB_iff.1 hD hc) i hi) hci

@[expose] def u3 (a : Mat4) (h : a * a * a = 1) : GL4 :=
  ⟨a, a * a, by rw [← mul_assoc]; exact h, h⟩

@[expose] def u2 (c : Mat4) (h : c * c = 1) : GL4 := ⟨c, c, h, h⟩

theorem conj_mul (g x y : GL4) : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group

theorem coe_enc (g : GL4) : ofCode (enc4 g) = (g : Mat4) := ofCode_enc4 g

theorem unit_of_nonSing {g : Mat4} (h : NonSing g) : ∃ u : GL4, (u : Mat4) = g := by
  have hinj : Function.Injective g.mulVec := by
    intro v w e
    have e' : g *ᵥ (v - w) = 0 := by rw [Matrix.mulVec_sub, e, sub_self]
    exact sub_eq_zero.mp (h _ e')
  obtain ⟨u, hu⟩ := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ⟨u, hu⟩

theorem classify : Certificates.S3x3GL42.Classify := by
  rintro a b c ⟨⟨ha, ha1, hb, hb1, hab⟩, hc, hca, hcb⟩
  set ga : GL4 := u3 a ha with hga
  set gb : GL4 := u3 b hb with hgb
  set gc : GL4 := u2 c hc with hgc
  have ea : (ga : Mat4) = a := rfl
  have eb : (gb : Mat4) = b := rfl
  have ec : (gc : Mat4) = c := rfl
  have uab : ga * gb = gb * ga := Units.ext (by rw [Units.val_mul, Units.val_mul, ea, eb, hab])
  have uca : gc * ga = ga * ga * gc :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, Units.val_mul, ea, ec, hca])
  have ucb : gc * gb = gb * gc := Units.ext (by rw [Units.val_mul, Units.val_mul, eb, ec, hcb])
  have ub3 : gb * gb * gb = 1 := Units.ext (by rw [Units.val_mul, Units.val_mul, eb, hb,
    Units.val_one])
  have uc2 : gc * gc = 1 := Units.ext (by rw [Units.val_mul, ec, hc, Units.val_one])
  obtain ⟨hA, -⟩ := facts_at ga
  obtain ⟨w, hw⟩ := hA ((o3_iff (enc4_lt ga)).2 ⟨by rw [coe_enc]; exact ha,
    by rw [coe_enc]; exact ha1⟩)
  obtain ⟨j, t, hj, ht, e⟩ := wW_spec hw
  obtain ⟨g, -, hg⟩ := ea_exact.1 j hj
  rw [← hg, coe_enc, coe_enc, ea] at e
  set A0 : Mat4 := ofCode (sA0 t) with hA0
  set B0 : Mat4 := ofCode (sB0 t) with hB0
  have eA : ((g * ga * g⁻¹ : GL4) : Mat4) = A0 := by
    rw [Units.val_mul, Units.val_mul, ea, e, mul_assoc, Units.mul_inv, mul_one]
  set b' : GL4 := g * gb * g⁻¹ with hb'
  have ub'A : b' * (g * ga * g⁻¹) = g * ga * g⁻¹ * b' := by
    rw [hb', conj_mul, conj_mul, uab]
  have hb'A : (b' : Mat4) * A0 = A0 * b' := by
    rw [← eA, ← Units.val_mul, ← Units.val_mul, ub'A]
  have hb'3 : (b' : Mat4) * b' * b' = 1 := by
    rw [← Units.val_mul, ← Units.val_mul, hb', conj_mul, conj_mul, ub3, mul_one, mul_inv_cancel,
      Units.val_one]
  have hb'1 : (b' : Mat4) ≠ 1 := by
    intro h1
    have : b' = 1 := Units.ext (by rw [h1, Units.val_one])
    rw [hb', mul_inv_eq_one, mul_eq_left] at this
    exact hb1 (by rw [← eb, this, Units.val_one])
  obtain ⟨-, hT⟩ := facts_at b'
  obtain ⟨hB, hC, -⟩ := hT t ht
  rcases hB ((o3_iff (enc4_lt b')).2 ⟨by rw [coe_enc]; exact hb'3, by rw [coe_enc]; exact hb'1⟩)
      ((commB_iff _ _).2 (by rw [coe_enc]; exact hb'A)) with ⟨v, hv⟩ | hbad
  · obtain ⟨hh, h1, h2⟩ := vW_spec hv
    obtain ⟨g2, -, hg2⟩ := ea_exact.1 _ hh
    rw [← hg2, coe_enc] at h1 h2
    rw [coe_enc] at h2
    have k1 : ((g2 * g : GL4) : Mat4) * a = A0 * (g2 * g : GL4) := by
      rw [Units.val_mul, mul_assoc, e, ← mul_assoc, h1, mul_assoc]
    have hgb' : (g : Mat4) * b = (b' : Mat4) * g := by
      rw [← eb, ← Units.val_mul, ← Units.val_mul, hb', inv_mul_cancel_right]
    have k2 : ((g2 * g : GL4) : Mat4) * b = B0 * (g2 * g : GL4) := by
      rw [Units.val_mul, mul_assoc, hgb', ← mul_assoc, h2, mul_assoc]
    refine ⟨((g2 * g : GL4) : Mat4), det_eq_one _, ?_⟩
    have ht' : t = 0 ∨ t = 1 := by omega
    obtain ⟨s1, s2, s3, s4⟩ := stdC
    rcases ht' with rfl | rfl
    · exact Or.inl ⟨k1.trans (by rw [hA0, s1]), k2.trans (by rw [hB0, s2])⟩
    · exact Or.inr ⟨k1.trans (by rw [hA0, s3]), k2.trans (by rw [hB0, s4])⟩
  · exfalso
    obtain ⟨i, hi, hbi⟩ := (inL_iff _ _ _).1 hbad
    set c' : GL4 := g * gc * g⁻¹ with hc'
    have hc'2 : (c' : Mat4) * c' = 1 := by
      rw [← Units.val_mul, hc', conj_mul, uc2, mul_one, mul_inv_cancel, Units.val_one]
    have hc'A : (c' : Mat4) * A0 = A0 * A0 * c' := by
      rw [← eA, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul, hc', conj_mul, conj_mul,
        conj_mul, uca]
    have hc'b : (c' : Mat4) * b' = b' * c' := by
      rw [← Units.val_mul, ← Units.val_mul, hc', hb', conj_mul, conj_mul, ucb]
    obtain ⟨-, hT3⟩ := facts_at c'
    obtain ⟨-, hC3, -⟩ := hT3 t ht
    obtain ⟨hn, -⟩ := hC3 ((sq_iff _).2 (by rw [coe_enc]; exact hc'2))
      ((mulEq_iff _ _ _ _).2 (by rw [coe_enc, mul4F_ofCode]; exact hc'A))
    have := hn i hi
    rw [hbi, notB_iff, commB_iff, coe_enc, coe_enc] at this
    exact this hc'b

theorem centS_at {t : ℕ} (ht : t < 2) {i l : ℕ} (hi : i < 3) (hl : l < 6)
    (h3 : ofCode (cT t i l) * ofCode (cT t i l) * ofCode (cT t i l) = 1) :
    ofCode (cT t i l) = 1 ∨ ofCode (cT t i l) = ofCode (sB0 t) ∨
      ofCode (cT t i l) = ofCode (sB0 t) * ofCode (sB0 t) := by
  have hc : centS t = true := by
    have ht' : t = 0 ∨ t = 1 := by omega
    rcases ht' with rfl | rfl
    · exact centS_ok.1
    · exact centS_ok.2
  unfold centS at hc
  have h := (allN_iff _ _).1 ((allN_iff _ _).1 hc i hi) l hl
  rw [letB_eq] at h
  have h' := impB_iff.1 h ((one_iff (mul4F_lt _ _)).2 (by rw [mul4F_ofCode, mul4F_ofCode]; exact h3))
  rcases orB_iff.1 h' with h1 | h1
  · left
    rw [beq_iff.1 h1, ofCode_id4]
  rcases orB_iff.1 h1 with h2 | h2
  · exact Or.inr (Or.inl (by rw [beq_iff.1 h2]))
  · exact Or.inr (Or.inr (by rw [beq_iff.1 h2, mul4F_ofCode]))

theorem std_of {t : ℕ} (ht : t < 2) {c : Mat4} (hc : RelC (ofCode (sA0 t)) (ofCode (sB0 t)) c) :
    (∃ i < 3, ofCode (cL t i) = c) ∧ CentFacts (ofCode (sA0 t)) (ofCode (sB0 t)) c := by
  obtain ⟨hc2, hca, hcb⟩ := hc
  set gc : GL4 := u2 c hc2 with hgc
  have ec : (gc : Mat4) = c := rfl
  obtain ⟨-, hT⟩ := facts_at gc
  obtain ⟨-, hC, -⟩ := hT t ht
  obtain ⟨-, hcl⟩ := hC ((sq_iff _).2 (by rw [coe_enc]; exact hc2))
    ((mulEq_iff _ _ _ _).2 (by rw [coe_enc, mul4F_ofCode]; exact hca))
  obtain ⟨i, hi, hci⟩ := (inL_iff _ _ _).1 (hcl ((commB_iff _ _).2 (by rw [coe_enc]; exact hcb)))
  have hci' : ofCode (cL t i) = c := by rw [hci, coe_enc, ec]
  refine ⟨⟨i, hi, hci'⟩, (List.range 6).map (fun l => ofCode (cT t i l)), by simp, ?_, ?_⟩
  · intro g hg1 hg2 hg3
    obtain ⟨gu, rfl⟩ := unit_of_nonSing hg3
    obtain ⟨-, hT'⟩ := facts_at gu
    obtain ⟨-, -, hD⟩ := hT' t ht
    have h := hD ((commB_iff _ _).2 (by rw [coe_enc]; exact hg1)) i hi
      ((commB_iff _ _).2 (by rw [coe_enc, hci']; exact hg2))
    obtain ⟨l, hl, e⟩ := (inL_iff _ _ _).1 h
    exact List.mem_map.2 ⟨l, List.mem_range.2 hl, by rw [e, coe_enc]⟩
  · intro g hg hg3
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hg
    exact centS_at ht hi (List.mem_range.1 hl) hg3

theorem stdI : StdI := by
  obtain ⟨s1, s2, -, -⟩ := stdC
  intro c hc
  have hc' : RelC (ofCode (sA0 0)) (ofCode (sB0 0)) c := by
    rw [s1, s2]
    exact hc.2
  obtain ⟨⟨i, hi, rfl⟩, hcent⟩ := std_of (by norm_num) hc'
  rw [s1, s2] at hcent
  exact ⟨hcent, typeI_ok i hi⟩

theorem irr_of {a b c : ℕ} (h : Irr3C a b c) : Irr (ofCode a) (ofCode b) (ofCode c) := by
  intro S h0 hadd hinv ⟨v, hvS, hv0⟩
  obtain ⟨s, hs, hsW⟩ := subspace_eq (subspaces_complete S h0 hadd)
  have hsl := (subC.2.2.1 s hs).2
  rcases h s hs (stab_of hsl hsW fun w hw => (hinv w hw).1)
      (stab_of hsl hsW fun w hw => (hinv w hw).2.1)
      (stab_of hsl hsW fun w hw => (hinv w hw).2.2) with rfl | rfl
  · exfalso
    rw [← hsW] at hvS
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq, Finset.mem_singleton, vecOfCode_zero] at hvS
    exact hv0 hvS
  · rw [← hsW, Finset.eq_univ_iff_forall]
    intro w
    obtain ⟨u, hu, rfl⟩ := vec_surj w
    rw [List.mem_toFinset]
    exact List.mem_map_of_mem (List.mem_range.2 hu)

theorem stdII : StdII := by
  obtain ⟨-, -, s3, s4⟩ := stdC
  intro c hc
  have hc' : RelC (ofCode (sA0 1)) (ofCode (sB0 1)) c := by
    rw [s3, s4]
    exact hc.2
  obtain ⟨⟨i, hi, rfl⟩, hcent⟩ := std_of (by norm_num) hc'
  rw [s3, s4] at hcent
  have hirr := irr_of (irr_ok i hi)
  rw [s3, s4] at hirr
  exact ⟨hcent, fpf_ok.1, fpf_ok.2, hirr⟩

end CertificateChecks.KernelMisc.GL4S3

end
