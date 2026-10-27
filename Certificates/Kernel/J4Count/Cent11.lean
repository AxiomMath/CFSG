
module


public import Certificates.Kernel.J4Count.KFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11Base1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentralizerH11Base

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelJ4Count.Cent11

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native
open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CertificateChecks.KernelJ4Count

theorem pow_1024_of_commute {k : J} (hk : k ∈ K) (hc : k * a276 = a276 * k) : k ^ 1024 = k := by
  obtain ⟨w, hw, hA⟩ := exists_actsBy_h11X hk hc
  have h1 := actsBy_pow 1024 hA
  rw [h11_cert.2.2.1 w hw] at h1
  exact eq_of_actsBy' (K.pow_mem hk 1024) hk h1 hA

theorem eq_one_or_card_lt_of_pow_three {k : J} (hk : k ∈ K) (hc : k * a276 = a276 * k)
    (h3 : k ^ 3 = 1) :
    k = 1 ∨ Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup J) < 4 := by
  obtain ⟨w, hw, hA⟩ := exists_actsBy_h11X hk hc
  have hXb := bounded_h11X hw
  have h1 := actsBy_pow 3 hA
  rw [h3] at h1
  have hp : powCols (h11X w) 3 = idRows 11 :=
    eq_of_actsBy_bounded h1 actsBy_one (bounded_powCols_h11 3 hXb)
      h11_cert.2.2.2.2.2
  rcases h11_cert.2.2.2.1 w hw hp with hid | hlt
  · left
    rw [hid] at hA
    exact eq_one_of_actsBy_id' hk hA
  · right
    rw [card_centralizer_N_of_actsBy hA (bounded_getD hXb)]
    exact hlt

theorem four_le_card_centralizer_three {h : J} (hh : h ∈ H) (ho : orderOf h = 3) :
    4 ≤ Nat.card (Subgroup.centralizer {h} ⊓ N : Subgroup J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_card_centralizer_of_sylow (Q3_le_K.trans K_le_H) card_Q3_sylow'
    conj_mem_N_of_mem_H (fun q hq h1 => ?_) hh ho
  obtain ⟨k, hk, rfl⟩ := mem_Q3_iff'.1 hq
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · exact absurd q3Elt_zero' h1
    · exact h
  rw [card_centralizer_N_of_actsBy (q3Elt_spec hk).2 (fun j hj => by
    rw [← getElem!_eq_getD']; exact (q3_all k hk).2.1 j hj)]
  exact h11_cert.2.2.2.2.1 k hk hk0

theorem orderOf_a276 : orderOf a276 = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine orderOf_eq_prime a276_pow' fun h1 => ?_
  have h2 : η 2 ∈ N := η_mem_N 2
  have := a276_fix h2 (by rw [h1]; group)
  rcases this with h | h
  · exact absurd (η_injOn (k := 0) (by norm_num) (by norm_num) (h.trans η_zero.symm)) (by norm_num)
  · exact absurd (η_injOn (k := 14) (by norm_num) (by norm_num) h) (by norm_num)

theorem card_centralizer_K_a276_le :
    Nat.card (Subgroup.centralizer {a276} ⊓ K : Subgroup J) ≤ 11 := by
  set D : Subgroup J := Subgroup.centralizer {a276} ⊓ K with hD
  have hDK : D ≤ K := inf_le_right
  have hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card D → p = 11 := by
    intro p hpp hdvd
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := D) p hdvd
    have hcD : (c : J) ∈ (Subgroup.centralizer {a276} ⊓ K : Subgroup J) := c.2
    have hcK : (c : J) ∈ K := (Subgroup.mem_inf.1 hcD).2
    have hcc : (c : J) * a276 = a276 * c := by
      have h := (Subgroup.mem_inf.1 hcD).1
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 h
      exact h2
    have ho : orderOf (c : J) = p := by rw [← hc]; exact (Subgroup.orderOf_coe c)
    have h1023 : (c : J) ^ 1023 = 1 := by
      have h := pow_1024_of_commute hcK hcc
      have e : (c : J) ^ 1024 = (c : J) * (c : J) ^ 1023 := by rw [← pow_succ']
      rw [e] at h
      exact (mul_eq_left.1 h)
    have hp1023 : p ∣ 1023 := ho ▸ orderOf_dvd_of_pow_eq_one h1023
    have hpK : p ∣ Nat.card K := (hdvd.trans (Subgroup.card_dvd_of_le hDK))
    rw [card_K_eq'] at hpK
    have h1023' : p ∣ 3 * 11 * 31 := by norm_num; exact hp1023
    rcases (Nat.Prime.dvd_mul hpp).1 h1023' with h | h
    · rcases (Nat.Prime.dvd_mul hpp).1 h with h | h
      · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h
        subst h3
        exfalso
        have hk3 : (c : J) ^ 3 = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
        rcases eq_one_or_card_lt_of_pow_three hcK hcc hk3 with h1 | hlt
        · rw [h1, orderOf_one] at ho
          omega
        · have := four_le_card_centralizer_three (K_le_H hcK) ho
          omega
      · exact (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h
    · exfalso
      have h31 : p = 31 := (Nat.prime_dvd_prime_iff_eq hpp (by norm_num)).1 h
      subst h31
      revert hpK
      norm_num
  have hm := Nat.eq_prime_pow_of_unique_prime_dvd (p := 11)
    (Nat.card_pos (α := D)).ne' fun {q} hq hdvd => hp q hq hdvd
  generalize (Nat.card D).primeFactorsList.length = m at hm
  rw [hm]
  by_contra hlt
  have hm2 : 2 ≤ m := by
    by_contra h
    have : m ≤ 1 := by omega
    interval_cases m <;> simp_all
  have h1 : 11 ^ 2 ∣ Nat.card K := by
    refine (pow_dvd_pow 11 hm2).trans ?_
    rw [← hm]
    exact Subgroup.card_dvd_of_le hDK
  rw [card_K_eq'] at h1
  revert h1
  norm_num

theorem card_centralizer_H_a276_le :
    Nat.card (Subgroup.centralizer {a276} ⊓ H : Subgroup J) ≤ 22 := by
  set C : Subgroup J := Subgroup.centralizer {a276} with hC
  let f : (C ⊓ N : Subgroup J) × (C ⊓ K : Subgroup J) → (C ⊓ H : Subgroup J) := fun p =>
    ⟨(p.1 : J) * p.2, Subgroup.mem_inf.2
      ⟨C.mul_mem (Subgroup.mem_inf.1 p.1.2).1 (Subgroup.mem_inf.1 p.2.2).1,
        H.mul_mem (N_le_H (Subgroup.mem_inf.1 p.1.2).2) (K_le_H (Subgroup.mem_inf.1 p.2.2).2)⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨hgC, hgH⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨n, hn, k, hk, hgnk⟩ := exists_mul_of_mem_H' hgH
    have hcomm : a276 * (n * k) = (n * k) * a276 := by
      rw [← hgnk]
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 hgC
      exact h2.symm
    have e1 : k * a276 * k⁻¹ * a276⁻¹ = n⁻¹ * (a276 * n * a276⁻¹) := by
      calc k * a276 * k⁻¹ * a276⁻¹ = n⁻¹ * (n * k * a276) * k⁻¹ * a276⁻¹ := by group
        _ = n⁻¹ * (a276 * (n * k)) * k⁻¹ * a276⁻¹ := by rw [← hcomm]
        _ = n⁻¹ * (a276 * n * a276⁻¹) := by group
    have hmem : k * a276 * k⁻¹ * a276⁻¹ ∈ K ⊓ N :=
      ⟨K.mul_mem (K.mul_mem (K.mul_mem hk a276_mem_K) (K.inv_mem hk)) (K.inv_mem a276_mem_K), by
        rw [e1]
        exact N.mul_mem (N.inv_mem hn) (conj_mem_N_of_mem_H _ a276_mem_H n hn)⟩
    rw [K_inf_N, Subgroup.mem_bot] at hmem
    have hka : a276 * k = k * a276 := by
      calc a276 * k = (k * a276 * k⁻¹ * a276⁻¹) * (a276 * k) := by rw [hmem, one_mul]
        _ = k * a276 := by group
    have hkC : k ∈ C := by
      have h2 : k * a276 = a276 * k := hka.symm
      exact Subgroup.mem_centralizer_singleton_iff.2 h2
    have hnC : n ∈ C := by
      have h2 : n * a276 = a276 * n := by
        refine mul_right_cancel (b := k) ?_
        calc n * a276 * k = n * (a276 * k) := by group
          _ = n * (k * a276) := by rw [hka]
          _ = n * k * a276 := by group
          _ = a276 * (n * k) := hcomm.symm
          _ = a276 * n * k := by group
      exact Subgroup.mem_centralizer_singleton_iff.2 h2
    exact ⟨(⟨n, Subgroup.mem_inf.2 ⟨hnC, hn⟩⟩, ⟨k, Subgroup.mem_inf.2 ⟨hkC, hk⟩⟩),
      Subtype.ext hgnk.symm⟩
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod] at h1
  have h2 := card_centralizer_N_a276_le
  have h3 := card_centralizer_K_a276_le
  calc Nat.card (C ⊓ H : Subgroup J) ≤ Nat.card (C ⊓ N : Subgroup J) * Nat.card (C ⊓ K : Subgroup J) :=
        h1
    _ ≤ 2 * 11 := Nat.mul_le_mul h2 h3

theorem factorization_H_eleven : (Nat.card H).factorization 11 = 1 := by
  have h2 : Nat.Prime 2 := Nat.prime_two
  have h3 : Nat.Prime 3 := by norm_num
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  rw [card_H_eq']
  repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow h2, Nat.Prime.factorization_pow h3,
    Nat.Prime.factorization h5, Nat.Prime.factorization h7, Nat.Prime.factorization h11,
    Nat.Prime.factorization h23, Finsupp.single_apply]
  norm_num

theorem card_centralizer_H_eleven_le :
    ∀ h ∈ Hj, orderOf h = 11 →
      Nat.card ↥(Subgroup.centralizer ({h} : Set J) ⊓ Hj) ≤ 22 := by
  intro h hh ho
  rw [← H_eq_Hj'] at hh ⊢
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have e := card_centralizer_inf_eq (K := H) (N := H) factorization_H_eleven
    (fun g hg n hn => H.mul_mem (H.mul_mem hg hn) (H.inv_mem hg)) hh a276_mem_H ho orderOf_a276
  rw [e]
  exact card_centralizer_H_a276_le

end CertificateChecks.KernelJ4Count.Cent11

end
