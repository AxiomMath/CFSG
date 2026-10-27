module

public import Certificates.Kernel.HNFFib.Facts
public import Certificates.Kernel.HNFOrb.Checks1
public import Certificates.Kernel.HNFOrb.Checks2
public import Certificates.Kernel.HNFOrb.Checks3a
public import Certificates.Kernel.HNFOrb.Checks3b
public import Certificates.Kernel.HNFOrb.Checks3c
public import CFSG.Certificates.Kernel.HNFOrbSound
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K

public section

namespace CertificateChecks.KernelHNFOrb

open CFSG.EvenSporadicStandard.Solomon78 CFSG.Sporadic.HNSchreier
open CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFOrb CFSG.KS.HNF26729 CFSG.KS.HNFOrb
open CFSG.KS.HNLocal CertificateChecks.KernelHNF26720 CertificateChecks.KernelHNF26729
open CertificateChecks.KernelHNFFib CFSG.KD.HNFOrb

theorem orb_bound {i N : ℕ} (hi : i < 9) {u : ℕ} {mv ks : List (List ℕ)} {ord : List ℕ}
    (hch : ∀ j < ks.length, CFSG.KD.HNFOrb.chunkW hnfW1 hnfW2 hnfRepWords[i]! u (getL mv j)
      (getL ks j) = true)
    (hd : distOK (flat ks) ord N = true) :
    N ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[i]!)).ncard := by
  have hfin : Finite ↥JH := Finite.of_injective ρJ ρJ_injective
  have cBi' : CFSG.KS.Ord.Canon 5 133 13 CFSG.KD.HNF26729.Bi := cBi
  have hg1 : ρJ hnfG1 = MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi hnfW1 := (mw_eq w1_valid).symm
  have hg2 : ρJ hnfG2 = MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi hnfW2 := (mw_eq w2_valid).symm
  have hg1i : ρJ hnfG1⁻¹ = MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi (invW hnfW1) := (mw_inv w1_valid).symm
  have hg2i : ρJ hnfG2⁻¹ = MW (CFSG.KD.FamHNSeed.RW 1) (CFSG.KD.FamHNSeed.RW 2)
      CFSG.KD.HNF26729.Bi (invW hnfW2) := (mw_inv w2_valid).symm
  have m1 : hnfG1 ∈ hnfC0 := Subgroup.subset_closure (by simp)
  have m2 : hnfG2 ∈ hnfC0 := Subgroup.subset_closure (by simp)
  have mA : aJ ∈ hnfC0 := Subgroup.subset_closure (by simp)
  exact orbit_bound CFSG.KD.FamHNSeed.consts cA cB cBi' hch hd ρJ hnfC0
    (hnfRep hnfRepWords[i]!) (ρ_rep hi) ⟨hnfG1, m1, hg1, hg1i⟩ ⟨hnfG2, m2, hg2, hg2i⟩
    ⟨aJ, mA, ρ_aJ, ρ_aJ_inv⟩

theorem bound1 : 1408 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[1]!)).ncard := by
  refine orb_bound (u := O1.u) (mv := O1.mv) (by norm_num) (fun j hj => ?_) d1
  have h8 : j < 8 := hj
  interval_cases j
  exacts [c1_0, c1_1, c1_2, c1_3, c1_4, c1_5, c1_6, c1_7]

theorem bound2 : 2200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[2]!)).ncard := by
  refine orb_bound (u := O2.u) (mv := O2.mv) (by norm_num) (fun j hj => ?_) d2
  have h11 : j < 11 := hj
  interval_cases j
  exacts [c2_0, c2_1, c2_2, c2_3, c2_4, c2_5, c2_6, c2_7, c2_8, c2_9, c2_10]

theorem bound3 : 5775 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[3]!)).ncard := by
  refine orb_bound (u := O3.u) (mv := O3.mv) (by norm_num) (fun j hj => ?_) d3
  have h29 : j < 29 := hj
  interval_cases j
  exacts [c3_0, c3_1, c3_2, c3_3, c3_4, c3_5, c3_6, c3_7, c3_8, c3_9, c3_10, c3_11, c3_12, c3_13,
    c3_14, c3_15, c3_16, c3_17, c3_18, c3_19, c3_20, c3_21, c3_22, c3_23, c3_24, c3_25, c3_26,
    c3_27, c3_28]

end CertificateChecks.KernelHNFOrb

end
