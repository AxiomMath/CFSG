module

public import Certificates.Kernel.Misc.Perm.GH23LatJ
public import Certificates.Kernel.Misc.Perm.GH23LatC0
public import Certificates.Kernel.Misc.Perm.GH23LatC1
public import Certificates.Kernel.Misc.Perm.GH23LatC2
public import Certificates.Kernel.Misc.Perm.GH23LatC3
public import Certificates.Kernel.Misc.Perm.GH23LatC4
public import Certificates.Kernel.Misc.Perm.GH23LatC5
public import Certificates.Kernel.Misc.Perm.GH23LatC6
public import Certificates.Kernel.Misc.Perm.GH23LatC7
public import Certificates.Kernel.Misc.Perm.GH23Facts
public import CFSG.Certificates.Kernel.Misc.PermGH23LatSound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Ind
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutGH23Top
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CertificateChecks.KernelMisc.GH23Lat

open Equiv CFSG.KC.LQT CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CertificateChecks.KernelMisc.GH23
  CFSG.OddStandard.SmallF3.HarrisU33.GH23Data CFSG.OddStandard.SmallF3.HarrisU33.Outside

theorem lat_cov_of_slices {W : ℕ → ℕ} {m0 : ℕ} (h : ∀ s < 50, covS W m0 s = true) (d : ℕ)
    (hd : d < 5) (k : ℕ) (hk : k < 20160) :
    ∃ W' : ℕ → ℕ, covAt (eM (m0 + d)) (eM 40) (RA (m0 + d)) W' (NN (m0 + d)) (nR (m0 + d)) k =
      true := by
  have h1 := h (10 * d + k / 2016) (by omega)
  unfold covS at h1
  simp only [P.letB_eq] at h1
  have e1 : Nat.div (10 * d + k / 2016) 10 = d := by
    change (10 * d + k / 2016) / 10 = d
    omega
  have e2 : Nat.mod (10 * d + k / 2016) 10 = k / 2016 := by
    change (10 * d + k / 2016) % 10 = k / 2016
    omega
  rw [e1, e2] at h1
  refine ⟨_, (allR_iff _ _ _).1 h1 k ?_ ?_⟩
  · change 2016 * (k / 2016) ≤ k
    omega
  · change k < 2016 * (k / 2016) + 2016
    omega

theorem lat_cov (i : ℕ) (hi : i < 40) (k : ℕ) (hk : k < 20160) :
    ∃ W : ℕ → ℕ, covAt (eM i) (eM 40) (RA i) W (NN i) (nR i) k = true := by
  obtain ⟨c, d, hd, rfl⟩ : ∃ c d, d < 5 ∧ i = 5 * c + d :=
    ⟨i / 5, i % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  have hc : c < 8 := by omega
  interval_cases c
  · exact lat_cov_of_slices (W := W0) (m0 := 0) CV0.all d hd k hk
  · exact lat_cov_of_slices (W := W1) (m0 := 5) CV1.all d hd k hk
  · exact lat_cov_of_slices (W := W2) (m0 := 10) CV2.all d hd k hk
  · exact lat_cov_of_slices (W := W3) (m0 := 15) CV3.all d hd k hk
  · exact lat_cov_of_slices (W := W4) (m0 := 20) CV4.all d hd k hk
  · exact lat_cov_of_slices (W := W5) (m0 := 25) CV5.all d hd k hk
  · exact lat_cov_of_slices (W := W6) (m0 := 30) CV6.all d hd k hk
  · exact lat_cov_of_slices (W := W7) (m0 := 35) CV7.all d hd k hk

theorem lat_join (i : ℕ) (hi : i < 40) (j : ℕ) (hj : j < nR i) :
    RA i j < NN 40 ∧ ∃ t < 41, ∀ ρ : Perm (Fin 8), gh23Code ρ = eM 40 (RA i j) →
      gh23Sub (members.getD i ⟨[], .top⟩).gens ⊔ Subgroup.zpowers ρ =
        gh23Sub (members.getD t ⟨[], .top⟩).gens :=
  gh23_joinAt_sound (NA := NN 40) (R := rcd i j) (EA := eM 40) (NQ := NN) (NGQ := NG) (EQ := eM)
    (GQ := gM) (Qg := fun t => (members.getD t ⟨[], .top⟩).gens) (gens_ok i (by omega)) (member_exact i (by omega)).2 gens_ok
    (fun t ht => (member_exact t ht).2) ((P.allN_iff (nR i) (joinJ i)).1 (JK.all i hi) j hj)

theorem members_length : members.length = 41 := rfl

theorem lat_getD_mem (t : ℕ) (ht : t < 41) : members.getD t ⟨[], .top⟩ ∈ members := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (lt_of_lt_of_eq ht members_length.symm),
    Option.getD_some]
  exact List.getElem_mem _

theorem lat_member40 : gh23Sub (members.getD 40 ⟨[], .top⟩).gens = alternatingGroup (Fin 8) := by
  rw [← gh23_sub_topGens]
  rfl

theorem gh23Lat_join_closed : ∀ m ∈ members, ∀ σ ∈ alternatingGroup (Fin 8), ∃ m' ∈ members,
    gh23Sub m.gens ⊔ Subgroup.zpowers σ = gh23Sub m'.gens := by
  intro m hm σ hσ
  obtain ⟨i, hi0, he⟩ := List.getElem_of_mem hm
  have hi : i < 41 := lt_of_lt_of_eq hi0 members_length
  have he' : members.getD i ⟨[], .top⟩ = m := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi0, Option.getD_some, he]
  subst he'
  rw [← lat_member40] at hσ
  rcases Nat.lt_or_ge i 40 with hi40 | hi40
  · obtain ⟨k, hk, hkc⟩ := (member_exact 40 (by norm_num)).2.2.1 σ hσ
    rw [nn40] at hk
    obtain ⟨W, hW⟩ := lat_cov i hi40 k hk
    obtain ⟨j, hj, hcov⟩ := gh23_covAt_sound (member_exact i (by omega)).2 hW hkc
    obtain ⟨hra, t, ht, hjoin⟩ := lat_join i hi40 j hj
    obtain ⟨ρ, -, hρ⟩ := (member_exact 40 (by norm_num)).2.1 _ hra
    obtain ⟨π, hπ, κ, hκ, rfl⟩ := hcov ρ hρ
    refine ⟨_, lat_getD_mem t ht, ?_⟩
    rw [gh23_sup_zpowers_dc _ hπ hκ ρ]
    exact hjoin ρ hρ
  · obtain rfl : i = 40 := by omega
    refine ⟨_, lat_getD_mem 40 (by norm_num), ?_⟩
    rw [sup_eq_left, Subgroup.zpowers_le]
    exact hσ

end CertificateChecks.KernelMisc.GH23Lat

end
