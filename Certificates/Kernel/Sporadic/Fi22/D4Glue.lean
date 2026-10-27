module

public import Certificates.Kernel.Sporadic.Fi22.D4Chk
public import Certificates.Kernel.Sporadic.Fi22.FivePinSound
public import Certificates.Kernel.Sporadic.Fi22.FiveK
public import Certificates.Kernel.OmegaEight.Bridge3009
public import CFSG.Certificates.Kernel.Fi22D4Sound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.NativeValidSchreier
public import Certificates.Data.Fi22FiveD4
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeBridgeBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Monster.B.Fischer.Fi22Centralizer
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22D4

open CFSG.KC.Enum CFSG.KC.Fi22D4 CFSG.KC.PermWit CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSpor
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight CFSG.Certificates
open CFSG.Certificates.Native

theorem parts : ltL ordList 4096 = true ∧ bijK (packL ordList) (Fi22D4T 0) = true ∧
    allN 6 (fun j => presK (packL ordList) (Fi22D4T 0) (Fi22Pin.pin j)) = true ∧
    outK (packL ordList) (Fi22D4T 0) (Fi22W.W [1]) = true ∧
    resK (packL ordList) (Fi22D4T 1) (Fi22Pin.pin 6) = true ∧
    resK (packL ordList) (Fi22D4T 2) (Fi22Pin.pin 7) = true ∧
    siftR 360 9 KernelO8.AQ.LR KernelO8.AQ.TRI KernelO8.AQ.BP 7 (Fi22D4T 1) = true ∧
    siftR 360 9 KernelO8.AQ.LR KernelO8.AQ.TRI KernelO8.AQ.BP 7 (Fi22D4T 2) = true ∧
    faithK (packL ordList) (Fi22Pin.pin 0) (Fi22Pin.pin 1) = true := by
  have h := ok
  unfold d4K at h
  simp only [Fi22C9554.strictB_eq, Bool.and_eq_true, and_assoc] at h
  exact h

theorem ordList_length : ordList.length = 360 := rfl

theorem ord_lt : ∀ a ∈ ordList, a < 4096 := ltL_spec _ _ parts.1

theorem hO {k : Nat} (hk : k < ordList.length) : f12 (packL ordList) k = ordList[k] :=
  f12_packL _ ord_lt k hk

theorem bij {k : Nat} (hk : k < ordList.length) :
    ordList[k] < 3510 ∧ f9 (Fi22D4T 0) ordList[k] = k := by
  have h := bijK_spec parts.2.1 (k := k) (by rwa [ordList_length] at hk)
  rwa [hO hk] at h

theorem pos_ge {q : Nat} (h : 360 ≤ f9 (Fi22D4T 0) q) : q ∉ ordList := by
  intro hq
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 hq
  rw [(bij hm).2] at h
  rw [ordList_length] at hm
  omega

theorem set_facts : ordList.length = 360 ∧ ordList.Nodup ∧ ∀ p ∈ ordList, p < 3510 := by
  refine ⟨ordList_length, ?_, fun p hp => ?_⟩
  · rw [List.nodup_iff_injective_get]
    intro i j hij
    simp only [List.get_eq_getElem] at hij
    apply Fin.ext
    rw [← (bij i.2).2, ← (bij j.2).2, hij]
  · obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hp
    exact (bij hk).1

theorem at_eq {P : Nat} {g : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) g)
    (p : Fin 3510) : f12 P p = (g p : ℕ) :=
  Fi22C9554.at_of_rep h p p.2

theorem pres_of {j : Nat} (hj : j < 6) {g : Equiv.Perm (Fin 3510)}
    (hg : Rep 3510 (unpack 3510 12 (Fi22Pin.pin j)) g) (p : Fin 3510) (hp : (p : ℕ) ∈ ordList) :
    ((g p : Fin 3510) : ℕ) ∈ ordList := by
  obtain ⟨k, hk, hkp⟩ := List.mem_iff_getElem.1 hp
  have h := presK_spec (allN_spec parts.2.2.1 j hj) (k := k) (by rwa [ordList_length] at hk)
  rw [hO hk, hkp, at_eq hg p] at h
  rw [← h.2]
  have hm : f9 (Fi22D4T 0) (g p : ℕ) < ordList.length := by rw [ordList_length]; exact h.1
  rw [hO hm]
  exact List.getElem_mem hm

theorem pres_facts : ∀ t ∈ [xA, yA, hA, n1A, n2A, zA], ∀ g : Equiv.Perm (Fin 3510), Rep 3510 t g →
    ∀ p : Fin 3510, (p : ℕ) ∈ ordList → ((g p : Fin 3510) : ℕ) ∈ ordList := by
  intro t ht g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Fi22Pin.x_eq] at hg
    exact pres_of (j := 0) (by norm_num) hg
  · rw [Fi22Pin.y_eq] at hg
    exact pres_of (j := 1) (by norm_num) hg
  · rw [Fi22Pin.h_eq] at hg
    exact pres_of (j := 2) (by norm_num) hg
  · rw [Fi22Pin.n1_eq] at hg
    exact pres_of (j := 3) (by norm_num) hg
  · rw [Fi22Pin.n2_eq] at hg
    exact pres_of (j := 4) (by norm_num) hg
  · rw [Fi22Pin.z_eq] at hg
    exact pres_of (j := 5) (by norm_num) hg

theorem letters1 : lettersK 2 [1] = true := by quickRfl

theorem out_fact : ∀ g : Equiv.Perm (Fin 3510), Rep 3510 (evalW [1]) g →
    ∃ p : Fin 3510, (p : ℕ) ∈ ordList ∧ ((g p : Fin 3510) : ℕ) ∉ ordList := by
  intro g hg
  rw [Fi22FiveK.eval_eq letters1] at hg
  obtain ⟨k, hk, hge⟩ := outK_spec parts.2.2.2.1
  have hk' : k < ordList.length := by rw [ordList_length]; exact hk
  refine ⟨⟨ordList[k], (bij hk').1⟩, List.getElem_mem hk', pos_ge ?_⟩
  have e := at_eq hg ⟨ordList[k], (bij hk').1⟩
  change f12 (Fi22W.W [1]) ordList[k] = _ at e
  rw [← e, ← hO hk']
  exact hge

theorem mem_autT_of_sift {t : Array ℕ} {σ : Equiv.Perm (Fin 360)}
    (ht : Rep 360 t σ)
    (h : siftA 360 (rawLevels 360 autS ((autBase.map Fin.val).toArray))
      ((autBase.map Fin.val).toArray) 0 t = true) : σ ∈ autT := by
  have hc := autChain_ok.1
  have hA := chainArrays_ofArrays (n := 360) (hn := by norm_num) (S := autS) (k := 10)
    (hk := by rw [autS_size]; norm_num) (base := autBase) (hb := by decide)
    (W := wordsOf 10 autWords) (chainCheckFacts hc).strong_inv
  exact (siftA_iff_mem_originalSubgroup hA (by norm_num) hc ht).1 h

theorem res_of {T R : Nat}
    (hres : resK (packL ordList) R T = true)
    (hs : siftR 360 9 KernelO8.AQ.LR KernelO8.AQ.TRI KernelO8.AQ.BP 7 R = true)
    {g : Equiv.Perm (Fin 3510)} (hg : Rep 3510 (unpack 3510 12 T) g) (σ : Equiv.Perm (Fin 360))
    (hσ : ∀ (k : Fin 360) (p : Fin 3510), (p : ℕ) = ordList[(k : ℕ)]! →
      ((g p : Fin 3510) : ℕ) = ordList[((σ k : Fin 360) : ℕ)]!) : σ ∈ autT := by
  refine mem_autT_of_sift (t := unpack 360 9 R) ?_ (siftR_sound KernelO8.bindsAQ
    (KernelO8.perm_of_head KernelO8.AQ.head) KernelO8.AQ.hl hs)
  intro k
  rw [CFSG.KC.Misc.PairCount.unpack_get k.2]
  change f9 R k = (σ k : ℕ)
  have hk : (k : ℕ) < ordList.length := by rw [ordList_length]; exact k.2
  have hσk : ((σ k : Fin 360) : ℕ) < ordList.length := by rw [ordList_length]; exact (σ k).2
  obtain ⟨hR, hRe⟩ := resK_spec hres k.2
  have hRl : f9 R k < ordList.length := by rw [ordList_length]; exact hR
  have e := hσ k ⟨ordList[(k : ℕ)], (bij hk).1⟩ (getElem!_pos ordList (k : ℕ) hk).symm
  rw [getElem!_pos ordList _ hσk] at e
  rw [hO hk, at_eq hg ⟨ordList[(k : ℕ)], (bij hk).1⟩, e, hO hRl] at hRe
  rw [← (bij hRl).2, hRe, (bij hσk).2]

theorem res_facts : ∀ t ∈ [g1A, g2A], ∀ g : Equiv.Perm (Fin 3510),
    Rep 3510 t g → ∀ σ : Equiv.Perm (Fin 360),
      (∀ (k : Fin 360) (p : Fin 3510), (p : ℕ) = ordList[(k : ℕ)]! →
        ((g p : Fin 3510) : ℕ) = ordList[((σ k : Fin 360) : ℕ)]!) → σ ∈ autT := by
  intro t ht g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · rw [Fi22Pin.g1_eq] at hg
    exact res_of parts.2.2.2.2.1 parts.2.2.2.2.2.2.1 hg
  · rw [Fi22Pin.g2_eq] at hg
    exact res_of parts.2.2.2.2.2.1 parts.2.2.2.2.2.2.2.1 hg

theorem itK_eq {P : Nat} {g : Equiv.Perm (Fin 3510)} (h : Rep 3510 (unpack 3510 12 P) g)
    (p : Fin 3510) : ∀ n : Nat, itK P n p = ((g ^ n) p : ℕ)
  | 0 => rfl
  | n + 1 => by
    rw [itK_succ, itK_eq h p n, pow_succ', Equiv.Perm.mul_apply]
    exact at_eq h _

theorem faith_fact : ∀ X Y : Equiv.Perm (Fin 3510), Rep 3510 xA X → Rep 3510 yA Y →
    ∀ i j : ℕ, i < 5 → j < 5 → (i ≠ 0 ∨ j ≠ 0) →
      ∃ p : Fin 3510, (p : ℕ) ∈ ordList ∧ (X ^ i * Y ^ j) p ≠ p := by
  intro X Y hX hY i j hi hj hij
  rw [Fi22Pin.x_eq] at hX
  rw [Fi22Pin.y_eq] at hY
  obtain ⟨k, hk, hne⟩ := faithK_spec parts.2.2.2.2.2.2.2.2 hi hj hij
  have hk' : k < ordList.length := by rw [ordList_length]; exact hk
  refine ⟨⟨ordList[k], (bij hk').1⟩, List.getElem_mem hk', fun he => hne ?_⟩
  have e1 : f12 (packL ordList) k = ((⟨ordList[k], (bij hk').1⟩ : Fin 3510) : ℕ) := hO hk'
  rw [e1, itK_eq hY, itK_eq hX, ← Equiv.Perm.mul_apply, he]

end CertificateChecks.KernelSpor.Fi22D4

end
