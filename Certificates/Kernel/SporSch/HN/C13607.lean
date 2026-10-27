
module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenInputs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.HNElevenBase
public import CFSG.Mathlib.GroupTheory.PrimeOrderFix
public import CFSG.Sporadic.HNSchreier.Primitive
public import Certificates.Kernel.SporSch.HN.C13607K
public import Certificates.Kernel.SporSch.HN.C13607Nat
public import Certificates.Kernel.SporSch.HN.Pt2085

public section

namespace CertificateChecks.KernelSporSch.HN13607

open Equiv Subgroup
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native
open CFSG.KS.HNArr CFSG.KS.HNNat CFSG.KS.TW CFSG.KC.LL.HNX CFSG.KD.HN13607
open CertificateChecks.KernelSporSch.HNPt2109 CertificateChecks.KernelSporSch.HNPt2085
open CertificateChecks.KernelSporSch.HNArrS

theorem pl_u : plettersOK 17 elevenWord = true := by decide +kernel

theorem nat_u : ∀ x < 12, elevenWord.foldr (GZ natF natFI) x = (natArr cyc11)[x]! := by
  decide +kernel

theorem nat_ok : elevenNatCheck () = true := by
  unfold elevenNatCheck natOK
  rw [pl_u, Bool.true_and]
  exact peq_maps fun x hx => by rw [natWord_pt letters_ok.2 hx, nat_u x hx]

theorem natWord_u : natWord elevenWord = sigma11 := by
  have hn := nat_ok
  unfold elevenNatCheck at hn
  rw [← natStrongArr_eq] at hn
  exact natWord_of_natOK prep_sigma11 hn

noncomputable abbrev phiP : HP →* Perm (Fin 12) :=
  (alternatingGroup (Fin 12)).subtype.comp (thetaP : HP →* alternatingGroup (Fin 12))

theorem phiP_inj : Function.Injective phiP :=
  Subtype.val_injective.comp thetaP.injective

noncomputable abbrev uP : HP := hjEquiv ⟨elevenJ, elevenJ_mem⟩

theorem phiP_u : phiP uP = sigma11 := by
  change (thetaJ ⟨elevenJ, elevenJ_mem⟩ : Perm (Fin 12)) = sigma11
  rw [← natWord_u]
  exact thetaJ_hWordH elevenWord

theorem orderOf_uP : orderOf uP = 11 := by
  rw [← orderOf_injective phiP phiP_inj, phiP_u, sigma11_isCycle.orderOf, sigma11_support_card]

theorem card_centralizer_uP : Nat.card (centralizer ({uP} : Set HP)) ≤ 11 := by
  rw [← card_centralizer_sigma11, ← card_map_of_injective phiP_inj]
  refine card_le_of_le ?_
  rintro _ ⟨c, hc, rfl⟩
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hc
  rw [mem_centralizer_singleton_iff, ← phiP_u, ← map_mul, ← map_mul, hc]

theorem not_sq_dvd : ¬ 11 ^ 2 ∣ Nat.card HP := by
  rw [rhoH_injective_card.2]
  norm_num [Nat.factorial]

theorem sizes_eleven : (∀ j : Fin 12, ¬ 11 ∣ Data.subgroupOrbitSizes[j.val]! →
    Data.subgroupOrbitSizes[j.val]! % 11 = 1) ∧
    (Finset.univ.filter fun j : Fin 12 => ¬ 11 ∣ Data.subgroupOrbitSizes[j.val]!).card = 4 := by
  decide +kernel

theorem fx_lt : ∀ k < 4, lget FXE k < nPts ∧ lget FXE k < nPts := by
  rw [codes_ok.2.2]
  decide

theorem fix_getD_inj : ∀ a b : Fin 4, elevenFix.getD a 0 = elevenFix.getD b 0 → a = b := by
  decide

theorem fix_pts {i : ℕ} (hi : i ∈ elevenFix) :
    ∃ h : i < hnsData.n, elevenJ • (⟨i, h⟩ : X) = ⟨i, h⟩ := by
  obtain ⟨hc, hm⟩ := strong_elem w_UW.1 codes_ok.1 letters_ok.2
  have hp := fx_U
  rw [← t_UW.1] at hp
  have hk : ∃ k < 4, lget FXE k = i := by
    rw [codes_ok.2.2]
    simp only [elevenFix, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
      ⟨3, by norm_num, rfl⟩]
  obtain ⟨k, hk4, rfl⟩ := hk
  have hlt := (fx_lt k hk4).1
  have h := gi_fn hc hm hp fx_lt hk4
  rw [wJ_sL _ letters_ok.2, gi_of_lt _ hlt] at h
  exact ⟨hlt, Fin.ext h⟩

theorem fix_iff (x : X) : elevenJ • x = x ↔ x.val ∈ elevenFix := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine ⟨fun hx => ?_, fun hm => ?_⟩
  · set S := Finset.univ.filter fun j : Fin 12 => ¬ 11 ∣ Data.subgroupOrbitSizes[j.val]!
    set F := Finset.univ.filter fun y : X => elevenJ • y = y
    set K := Finset.univ.filter fun y : X => y.val ∈ elevenFix
    have hcard : ∀ y : X, Nat.card (MulAction.orbit HP y) =
        Data.subgroupOrbitSizes[(hLab y).val]! := fun y => by
      rw [MulAction.orbit_eq_iff.2 (mem_orbit_hLab y), card_orbit]
    have hS : ∀ y ∈ F, hLab y ∈ S := fun y hy => by
      have hy' : uP • y = y := (Finset.mem_filter.1 hy).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [← hcard]
      exact CFSG.PrimeOrderFix.not_dvd_card_orbit orderOf_uP not_sq_dvd hy'
    have hinj : Set.InjOn hLab (F : Set X) := fun y hy z hz he => by
      have hy' : uP • y = y := (Finset.mem_filter.1 hy).2
      have hz' : uP • z = z := (Finset.mem_filter.1 hz).2
      have hyo := mem_orbit_hLab y
      have hzo := mem_orbit_hLab z
      rw [he] at hyo
      have hO : Nat.card (MulAction.orbit HP (repX (hLab z))) % 11 = 1 := by
        rw [card_orbit]
        exact sizes_eleven.1 _ (Finset.mem_filter.1 (hS z hz)).2
      exact CFSG.PrimeOrderFix.fix_orbit_eq orderOf_uP not_sq_dvd card_centralizer_uP hO hyo
        hzo hy' hz'
    have hF : F.card ≤ 4 :=
      (Finset.card_le_card_of_injOn hLab (by intro y hy; exact hS y hy) hinj).trans
        sizes_eleven.2.le
    have hKF : K ⊆ F := fun y hy => by
      obtain ⟨h, hf⟩ := fix_pts (Finset.mem_filter.1 hy).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hf⟩
    have hlt : ∀ k : Fin 4, elevenFix.getD k 0 < hnsData.n := by
      rw [hns_n]
      decide
    have hK : 4 ≤ K.card := by
      have h := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin 4))) (t := K)
        (fun k => (⟨elevenFix.getD k 0, hlt k⟩ : X))
        (by
          intro k _
          refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
          change elevenFix.getD k 0 ∈ elevenFix
          revert k
          decide)
        (by
          intro a _ b _ hab
          exact fix_getD_inj a b (congrArg Fin.val hab))
      simpa using h
    have hKe : K = F := Finset.eq_of_subset_of_card_le hKF (hF.trans hK)
    have hxF : x ∈ F := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩
    rw [← hKe] at hxF
    exact (Finset.mem_filter.1 hxF).2
  · obtain ⟨h, hf⟩ := fix_pts hm
    exact hf

theorem eleven_ok : elevenChecksO (hnsData.orbit ()) = true := by
  unfold elevenChecksO elevenChecksR
  rw [← hRegs_eq, ← hStrongArr_eq]
  unfold elevenChecksH
  rw [pl_u, Bool.true_and, beq_iff_eq]
  unfold fixedSet
  refine List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _) (by decide) fun i => ?_
  rw [List.mem_filter, List.mem_range, Array.all_eq_true_iff_forall_mem]
  simp only [List.mem_toArray, List.mem_singleton, forall_eq, beq_iff_eq]
  constructor
  · rintro ⟨hi, h1⟩
    rw [prep_hWord pl_u ⟨i, hi⟩, permJ_apply] at h1
    exact (fix_iff ⟨i, hi⟩).1 (Fin.ext h1)
  · intro hm
    obtain ⟨hi, hf⟩ := fix_pts hm
    refine ⟨hi, ?_⟩
    rw [prep_hWord pl_u ⟨i, hi⟩, permJ_apply]
    exact congrArg Fin.val hf

end CertificateChecks.KernelSporSch.HN13607

end
