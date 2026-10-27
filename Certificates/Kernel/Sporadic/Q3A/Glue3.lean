module

public import Certificates.Kernel.Sporadic.Q3A.Glue2

public section

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.Q3A.Check
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Q3AK
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

theorem actK_le (hv : ∀ i < 22880, vtOK i = true) (G i : Nat) : actK G i ≤ 22880 := by
  unfold actK
  rcases searchK_cases hv (keyF (imgK G (Q3AF i))) with h | ⟨h, -⟩ <;> omega

theorem adjK_iff {C v : Nat} : adjK C v = true ↔ actK C v < 22880 ∧ frootK (actK C v) = 10 := by
  unfold adjK
  rw [sB, band, nblt, nbeq]

theorem vdK_eq (y : Nat) : vdK y = if y < 22880 then dK (frootK y) else 4 := by
  unfold vdK
  rw [nIf_eq]
  by_cases h : y < 22880
  · rw [ite_eq_left (nblt.2 h), ite_eq_left h]
  · rw [ite_eq_right (fun e => h (nblt.1 e)), ite_eq_right h]

theorem dK_eq (r : Nat) : dK r = if r = 0 then 0 else if r = 10 then 1 else if r = 202 then 3 else 2 := by
  unfold dK
  simp only [nIf_eq, nbeq]

theorem vdK_one {y : Nat} : vdK y = 1 ↔ y < 22880 ∧ frootK y = 10 := by
  rw [vdK_eq, dK_eq]
  by_cases h : y < 22880
  · rw [ite_eq_left h]
    split_ifs <;> simp_all
  · rw [ite_eq_right h]
    simp [h]

theorem vdK_two {y : Nat} (h : vdK y = 2) : y < 22880 ∧ frootK y ≠ 10 := by
  rw [vdK_eq, dK_eq] at h
  by_cases hy : y < 22880
  · rw [ite_eq_left hy] at h
    refine ⟨hy, fun e => ?_⟩
    rw [e] at h
    simp at h
  · rw [ite_eq_right hy] at h
    omega

theorem n0_parts : countK 22880 (fun i => Nat.beq (frootK i) 10) = 486 ∧
    (∀ t, t + 1 < 486 → n0K t < n0K (t + 1)) ∧ ∀ t < 486, n0K t < 22880 ∧ frootK (n0K t) = 10 := by
  have h := kN0
  unfold n0OK at h
  rw [band, band] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨nbeq.1 h1, fun t ht => nblt.1 (allN_get h2 (by change t < 485; omega)), fun t ht => ?_⟩
  have := allN_get h3 ht
  rw [sB, band] at this
  exact ⟨nblt.1 this.1, nbeq.1 this.2⟩

section Checks

variable (hv : ∀ i < 22880, vtOK i = true) (hf : ∀ i < 22880, frOK i = true)
include hv hf

theorem isNbr0_iff (y : Nat) : isNbr0 y = true ↔ y < 22880 ∧ frootK y = 10 := by
  rw [isNbr0_eq hv hf, band, nblt, nbeq]

theorem nbr0_eq : nbr0 = ((List.range 486).map n0K).toArray := by
  apply Array.ext'
  unfold nbr0
  rw [Array.toList_filter, Array.toList_range, List.toList_toArray]
  rw [List.filter_congr (q := fun y => Nat.beq (frootK y) 10) fun y hy => ?_]
  · refine filter_range_eq (pairwise_of_succ n0_parts.2.1) (fun x hx => ?_) ?_
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      have := n0_parts.2.2 t (List.mem_range.1 ht)
      exact ⟨this.1, nbeq.2 this.2⟩
    · rw [← countK_eq, n0_parts.1, List.length_map, List.length_range]
  · rw [isNbr0_eq hv hf, (nblt.2 (List.mem_range.1 hy) : Nat.blt y 22880 = true)]

theorem nbrsOf_eq {i : Nat} (hi : i < 22880) :
    nbrsOf i = ((List.range 486).map fun t => actK (cA i) (n0K t)).toArray := by
  unfold nbrsOf
  rw [nbr0_eq hv hf]
  apply Array.ext'
  rw [Array.toList_map, List.toList_toArray, List.toList_toArray, List.map_map]
  refine List.map_congr_left fun t ht => ?_
  exact actIdx_eq hv (p_cArr hi) (n0_parts.2.2 t (List.mem_range.1 ht)).1

theorem rootDist_10 : rootDist 10 = 1 := by
  have h : isNbr0 10 = true := (isNbr0_iff hv hf 10).2 ⟨by norm_num, roots_parts.2.2.2.2.1⟩
  rw [rootDist, ite_eq_right (by decide), ite_eq_left h]

theorem not_nbr_root {r : Nat} (h : frootK r = r) (h10 : r ≠ 10) : isNbr0 r = false :=
  Bool.eq_false_iff.2 fun e => h10 (h ▸ ((isNbr0_iff hv hf r).1 e).2)

end Checks

end CertificateChecks.KernelSpor.Q3AG

end
