module

public import Certificates.Kernel.Sporadic.Fi22.Sq26560P
public import Certificates.Kernel.Sporadic.Fi22.C2066
public import Certificates.Kernel.Sporadic.Fi22.HypR1Glue
public import CFSG.Certificates.Kernel.Spor.Pc2BaseSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSquareFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Fi22Classes

public section

namespace CertificateChecks.KernelSpor.Fi22Sq26560

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.CommBase CFSG.Monster.B.Fischer
open CFSG.Sporadic.Schreier CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.Solomon78
open CFSG.EvenSporadicStandard.HypOne.Fi22

theorem prep_T : PRep 3510 12 T (fi22ExtRep 2) := by
  have h := rep_fi22ExtRep (k := 2) (by norm_num)
  rw [Fi22E2067.ext_eq (L := 21 + 2) (by norm_num)] at h
  exact prep_of_rep h

theorem base_sep
    (g : Equiv.Perm (Fin 3510)) (hg : g ∈ fi22P)
    (hfix : ∀ b ∈ Bs, ∀ h : b < 3510, g ⟨b, h⟩ = ⟨b, h⟩) : g = 1 := by
  refine Fi22C2066.fi22P_sep hg fun t ht h => ?_
  have ht' : t < 6 := ht
  interval_cases t <;> exact hfix _ (by simp [Bs]) h

theorem sylowSquareFacts :
    ∃ (S : Subgroup (Equiv.Perm (Fin 3510))) (d : Equiv.Perm (Fin 3510)),
      SylowSquareFacts (centralizerIn fi22P (fi22ExtRep 2)) S (fi22ExtRep 2) d := by
  have hl := lettersAll
  rw [bAnd_eq, Bool.and_eq_true, allN_iff, Nat.beq_eq] at hl
  obtain ⟨hl, h15⟩ := hl
  have hp := permAll
  rw [allN_iff] at hp
  have hex : ∀ k, k < 16 → ∃ g, g ∈ fi22P ∧ PRep 3510 12 (L k) g ∧ g * fi22ExtRep 2 = fi22ExtRep 2 * g := by
    intro k hk
    have h1 := hl k hk
    simp only [letterOK, bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h1
    obtain ⟨hc, hs, he⟩ := h1
    obtain ⟨g, hg, hr⟩ := Fi22R1.exists_mem_P hc (hp k hk) hs
    refine ⟨g, hg, hr, prep_unique (prep_pcomp (by norm_num) hr prep_T) ?_⟩
    change PRep 3510 12 (Fi22X.c (L k) T) _
    rw [he]
    exact prep_pcomp (by norm_num) prep_T hr
  choose! ℓ hℓP hℓR hℓC using hex
  have hK : ∀ k < 16, ℓ k ∈ centralizerIn fi22P (fi22ExtRep 2) := fun k hk =>
    mem_centralizerIn.2 ⟨hℓP k hk, hℓC k hk⟩
  have h15' : ℓ 15 = fi22ExtRep 2 := prep_unique (hℓR 15 (by norm_num)) (by rw [h15]; exact prep_T)
  obtain ⟨hcard, hdd, hd1, hdu, hdc, hcen, hns, hud⟩ :=
    CFSG.KC.Pc2Base.facts_of_pc2OK (H := fi22P) hℓR hℓP base_sep pcAll
  rw [h15'] at hdu hcen hud
  refine ⟨Subgroup.closure (ℓ '' Set.Ico 0 16), ℓ 14,
    { S_le := ?_, S_card := ?_, d_mem := hK 14 (by norm_num), d_sq := hdd, d_ne_one := hd1,
      d_ne_u := hdu, d_comm := hdc, center_inv := fun s hs _ hc => hcen s hs hc,
      d_nonsq := hns, ud_sq := hud }⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact hK k hk.2
  · rw [hcard, two_part_P (k := 2) (by norm_num)]
    rfl

end CertificateChecks.KernelSpor.Fi22Sq26560

end
