module

public import Certificates.Kernel.Fi22.FixLemmas
public import Certificates.Kernel.Fi22.Bray

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.Fi22F CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2

theorem letV_0 : letV tg 0 = tg 0 := by simp [letV]
theorem letV_1 : letV tg 1 = (tg 0)⁻¹ := by simp [letV]
theorem letV_2 : letV tg 2 = tg 1 := by simp [letV]
theorem letV_3 : letV tg 3 = (tg 1)⁻¹ := by simp [letV]

theorem cover {H : Subgroup PG} {rep : ℕ → PG} {LV : ℕ} (h0 : rep (lv LV 0) = 1)
    (hL : ∀ c < 4, ∃ L, Acts H rep LV L (letV tg c)) :
    ∀ g : PG, ∃ i < nP, g * (rep (lv LV i))⁻¹ ∈ H := by
  have step : ∀ (x y : PG) (c : ℕ), c < 4 → letV tg c = y →
      (∃ i < nP, x * (rep (lv LV i))⁻¹ ∈ H) → ∃ i < nP, x * y * (rep (lv LV i))⁻¹ ∈ H := by
    rintro x y c hc rfl ⟨i, hi, hx⟩
    obtain ⟨L, hLa⟩ := hL c hc
    obtain ⟨r, m⟩ := hLa i hi
    refine ⟨pf L i, r, ?_⟩
    have := H.mul_mem hx m
    simpa [mul_assoc] using this
  intro g
  have hg : g ∈ Subgroup.closure (tg '' {g | 2 * g < nat_lit 4}) := by
    rw [closure_tg]
    trivial
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨0, by decide, by rw [h0, inv_one, one_mul]; exact H.one_mem⟩
  | mul_right x _ y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    change 2 * k < 4 at hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact step x _ 0 (by norm_num) letV_0 ih
    · exact step x _ 2 (by norm_num) letV_2 ih
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨k, hk, rfl⟩ := hy
    change 2 * k < 4 at hk
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · exact step x _ 1 (by norm_num) letV_1 ih
    · exact step x _ 3 (by norm_num) letV_3 ih

theorem normalClosure_a : Subgroup.normalClosure {tg 0} = ⊤ := by
  set N := Subgroup.normalClosure ({tg 0} : Set PG)
  have ha : tg 0 ∈ N := Subgroup.subset_normalClosure rfl
  have hq : (QuotientGroup.mk' N) (tg 0) = 1 := (QuotientGroup.eq_one_iff _).mpr ha
  have hb11 : tg 1 ^ 11 ∈ N := by
    have h := congrArg (QuotientGroup.mk' N) ab_pow
    rw [map_pow, map_mul, hq, one_mul, map_one, ← map_pow] at h
    exact (QuotientGroup.eq_one_iff _).mp h
  have hb : tg 1 ∈ N := by
    have e : tg 1 = (tg 1 ^ 11) ^ 6 := by
      rw [← pow_mul, show 11 * 6 = 13 * 5 + 1 from rfl, pow_add, pow_mul, b_pow, one_pow, one_mul, pow_one]
    rw [e]
    exact N.pow_mem hb11 6
  rw [eq_top_iff, ← closure_tg, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  change 2 * k < 4 at hk
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact ha
  · exact hb

theorem center_of_fix {rep : ℕ → PG} {LV : ℕ} (h0 : rep (lv LV 0) = 1)
    (hL : ∀ c < 4, ∃ L, Acts HB rep LV L (letV tg c)) {z : PG}
    (hz : ∀ i < nP, rep (lv LV i) * z * (rep (lv LV i))⁻¹ ∈ HB) : z ∈ Subgroup.center PG := by
  have hconj : ∀ g : PG, g * z * g⁻¹ ∈ HB := by
    intro g
    obtain ⟨i, hi, hg⟩ := cover h0 hL g
    have := HB.mul_mem (HB.mul_mem hg (hz i hi)) (HB.inv_mem hg)
    simpa [mul_assoc] using this
  have hcomm : ∀ g : PG, z * (g⁻¹ * tg 0 * g) = (g⁻¹ * tg 0 * g) * z := by
    intro g
    have hc := Subgroup.mem_centralizer_iff.mp (a_cent (hconj g)) (tg 0) rfl
    have : g⁻¹ * (tg 0 * (g * z * g⁻¹)) * g = g⁻¹ * ((g * z * g⁻¹) * tg 0) * g := by rw [hc]
    simpa [mul_assoc] using this.symm
  have hle : Subgroup.normalClosure ({tg 0} : Set PG) ≤ Subgroup.centralizer {z} := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨_, rfl, hx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    have := hcomm g⁻¹
    simpa [mul_assoc] using this
  rw [normalClosure_a] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  have := Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) z rfl
  exact this.symm

end CertificateChecks.KernelFi22

end
