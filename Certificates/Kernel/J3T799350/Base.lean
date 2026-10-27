module

public import Certificates.Kernel.J3T799350.Glue
public import CFSG.Certificates.Kernel.Spor.RawOrbOutAgree

@[expose] public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelJ3T799350

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CertificateChecks.KernelSporSch
  CertificateChecks.KernelSpor CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Monster.B.Co2 CFSG.RankThree.PartTwo.Sec8.Hering611.J3T

theorem gen_eq : Orb.Gen 6156 j3StrongArrs 2 = j3P := by
  unfold Orb.Gen j3P
  rw [PJ3Check.range_two (fun j => permOfArr 6156 j3StrongArrs[j]!)]
  rfl


theorem prep_RT {r : Nat} (hr : r < 19) : Orb.PRep 6156 13 (RT r) (initG r) := by
  have hc : canonK 6156 13 (mask 13) (6156 * 13) (RT r) = true := by
    simpa using allBlk_spec canon r hr
  have h2 := co2Rep_natArr_iff.2 (rep_RT hr)
  rw [natArr_tabT hc] at h2
  exact Orb.prep_of_rep h2

theorem initG_two : initG 2 = j3u := by
  rw [initG.eq_1]
  simp

theorem prep_u : Orb.PRep 6156 13 (RT 2) j3u := by
  rw [← initG_two]
  exact prep_RT (by norm_num)

theorem fixb {g : Gp} (h0 : g 0 = 0) (h1 : g 1 = 1) (h3 : g 3 = 3) (h2 : g 2 = 2) :
    ∀ t < 4, ∀ hb : PairJ3.baseArr[t]! < 6156,
      g ⟨PairJ3.baseArr[t]!, hb⟩ = ⟨PairJ3.baseArr[t]!, hb⟩ := by
  intro t ht hb
  interval_cases t
  · have e : (⟨PairJ3.baseArr[0]!, hb⟩ : Fin 6156) = 0 := Fin.ext (by simp [PairJ3.baseArr])
    rw [e]; exact h0
  · have e : (⟨PairJ3.baseArr[1]!, hb⟩ : Fin 6156) = 1 := Fin.ext (by simp [PairJ3.baseArr])
    rw [e]; exact h1
  · have e : (⟨PairJ3.baseArr[2]!, hb⟩ : Fin 6156) = 3 := Fin.ext (by simp [PairJ3.baseArr])
    rw [e]; exact h3
  · have e : (⟨PairJ3.baseArr[3]!, hb⟩ : Fin 6156) = 2 := Fin.ext (by simp [PairJ3.baseArr])
    rw [e]; exact h2

theorem base_P {g : Gp} (hP : g ∈ Orb.Gen 6156 j3StrongArrs 2)
    (hf : ∀ t < 4, ∀ hb : PairJ3.baseArr[t]! < 6156,
      g ⟨PairJ3.baseArr[t]!, hb⟩ = ⟨PairJ3.baseArr[t]!, hb⟩) : g = 1 :=
  Orb.fix_one J3KT.hd PJ3Check.card_le ⟨hP, hf⟩

theorem not_out {q : Gp} (hq : q ∈ Orb.Gen 6156 j3StrongArrs 2)
    (hag : ∀ t ≤ 1, ∀ hb : PairJ3.baseArr[t]! < 6156,
      q ⟨PairJ3.baseArr[t]!, hb⟩ = j3u ⟨PairJ3.baseArr[t]!, hb⟩) : False :=
  Orb.not_agree_of_outK J3KT.hd PJ3Check.binds PJ3Check.perm PJ3.ho (by norm_num)
    PJ3Check.card_le (l := 1) (by norm_num) prep_u uOut hq hag

theorem inv_self_of_sq {G : Type*} [Group G] {x : G} (h : x ^ 2 = 1) : x⁻¹ = x := by
  rw [inv_eq_iff_mul_eq_one, ← sq, h]

theorem base_one_of {P R : Subgroup Gp} {u : Gp} {B : Nat → Prop}
    (hRmem : ∀ x, x ∈ R ↔ x ∈ P ∨ x * u ∈ P) (hu : u⁻¹ = u)
    (hP1 : ∀ g ∈ P, (∀ t, B t → ∀ hb : PairJ3.baseArr[t]! < 6156,
      g ⟨PairJ3.baseArr[t]!, hb⟩ = ⟨PairJ3.baseArr[t]!, hb⟩) → g = 1)
    (hout : ∀ q ∈ P, (∀ t, B t → ∀ hb : PairJ3.baseArr[t]! < 6156,
      q ⟨PairJ3.baseArr[t]!, hb⟩ = u ⟨PairJ3.baseArr[t]!, hb⟩) → False)
    {g : Gp} (hg : g ∈ R) (hf : ∀ t, B t → ∀ hb : PairJ3.baseArr[t]! < 6156,
      g ⟨PairJ3.baseArr[t]!, hb⟩ = ⟨PairJ3.baseArr[t]!, hb⟩) : g = 1 := by
  rcases (hRmem g).1 hg with hP | hPu
  · exact hP1 g hP hf
  · refine (hout _ (P.inv_mem hPu) fun t ht hb => ?_).elim
    have hgi : g⁻¹ ⟨PairJ3.baseArr[t]!, hb⟩ = ⟨PairJ3.baseArr[t]!, hb⟩ := by
      rw [Equiv.Perm.inv_eq_iff_eq]; exact (hf t ht hb).symm
    rw [mul_inv_rev, Equiv.Perm.mul_apply, hgi, hu]

theorem base_one {g : Gp} (hg : g ∈ j3R) (h0 : g 0 = 0) (h1 : g 1 = 1) (h3 : g 3 = 3)
    (h2 : g 2 = 2) : g = 1 := by
  obtain ⟨hU2, -, -, -, -, hRmem, -⟩ := ctuc_j3_normalizing_involution_permutation_model
  have hf := fixb h0 h1 h3 h2
  refine base_one_of (B := fun t => t < 4) hRmem (inv_self_of_sq hU2) (fun g' hg' hf' => ?_)
    (fun q hq hag => ?_) hg hf
  · rw [← gen_eq] at hg'
    exact base_P hg' hf'
  · rw [← gen_eq] at hq
    exact not_out hq fun t ht hb => hag t (by omega) hb

end CertificateChecks.KernelJ3T799350

end
