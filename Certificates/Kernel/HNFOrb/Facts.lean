module

public import Certificates.Kernel.HNFFib.Facts
public import Certificates.Kernel.HNFOrb.Checks1
public import Certificates.Kernel.HNFOrb.Checks2
public import Certificates.Kernel.HNFOrb.Checks3a
public import Certificates.Kernel.HNFOrb.Checks3b
public import Certificates.Kernel.HNFOrb.Checks3c
public import CFSG.Certificates.Kernel.HNFOrbSound
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import CFSG.Certificates.Kernel.Common.ForallTree

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

#kc_forall_tree walks1 (fun j => chunkL BT1 O1.u (getL O1.mv j) (getL O1.ks j) = true) 19
  CFSG.KD.HNFOrb.c1_

theorem bound1 : 1408 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[1]!)).ncard := by
  refine orb_bound (u := O1.u) (mv := O1.mv) (by norm_num) (fun j hj => ?_) d1
  have hj' : j < 19 := hj
  have h := walks1 j hj'
  exact (chunkW_eq BT1_eq _ _ _).trans h

#kc_forall_tree walks2 (fun j => chunkL BT2 O2.u (getL O2.mv j) (getL O2.ks j) = true) 33
  CFSG.KD.HNFOrb.c2_

theorem bound2 : 2200 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[2]!)).ncard := by
  refine orb_bound (u := O2.u) (mv := O2.mv) (by norm_num) (fun j hj => ?_) d2
  have hj' : j < 33 := hj
  have h := walks2 j hj'
  exact (chunkW_eq BT2_eq _ _ _).trans h

#kc_forall_tree walks3 (fun j => chunkL BT3 O3.u (getL O3.mv j) (getL O3.ks j) = true) 87
  CFSG.KD.HNFOrb.c3_

theorem bound3 : 5775 ≤ (conjOrb hnfC0 (hnfRep hnfRepWords[3]!)).ncard := by
  refine orb_bound (u := O3.u) (mv := O3.mv) (by norm_num) (fun j hj => ?_) d3
  have hj' : j < 87 := hj
  have h := walks3 j hj'
  exact (chunkW_eq BT3_eq _ _ _).trans h

end CertificateChecks.KernelHNFOrb

end
