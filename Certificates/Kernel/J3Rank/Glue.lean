module

public import Certificates.Kernel.J3Rank.Checks
public import Certificates.Kernel.Q16J3.Glue
public import CFSG.Certificates.Kernel.ElemAbColSound

public section

namespace CertificateChecks.KernelJ3Rank

open CFSG.KC.ElemAbCol CFSG.KC.Census CFSG.RankThree.Native CFSG.Sporadic.SmallOddCore
open CertificateChecks.KernelQ16J3

theorem j3rk_res : ∀ B : Subgroup (Equiv.Perm (Fin 32)),
    B ≤ Subgroup.closure (permsA 32 (q16J3G.map (unpackP 32 5))) →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 31 := by
  intro B hB hcomm hsq
  obtain ⟨hg, hc, hps⟩ := q16J3_canon
  exact card_le_of_colOK (K := 30) (by norm_num) (by norm_num)
    (fun p hp => Nat.blt_eq.mp (List.all_eq_true.1 hps p hp)) hg hc q16J3_enum j3rk_col hB
    hcomm hsq

theorem j3S_elemAb_card_le
    {B : Subgroup (Equiv.Perm (Fin 6156))} (hBS : B ≤ j3S)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 31 := by
  have hc : Nat.card ↥j3S = 256 := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial.2.1
  rw [j3S] at hc hBS
  refine card_le_of_res q16J3Pt q16J3Pt_injective ?_ ?_ (hc.le.trans q16J3_res.1.ge) j3rk_res hBS
    hcomm hsq
  · rintro g ⟨T, hT, rfl⟩ i
    have hT' : T ∈ j3SylowGenTbls := List.mem_toArray.1 hT
    rw [q16J3_tbls] at hT'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hT'
    exact ⟨_, q16J3_gen (List.mem_range.1 hk) i⟩
  · rintro σ ⟨k, hk, rfl⟩
    have hk' : k < 8 := by
      have : k < (q16J3G.map (unpackP 32 5)).size := hk
      rw [Array.size_map, q16J3_size'.1] at this
      exact this
    have hm : j3CentTbl (k + 1) ∈ j3SylowGenTbls := by
      rw [q16J3_tbls]
      exact List.mem_map.2 ⟨k, List.mem_range.2 hk', rfl⟩
    refine ⟨_, ⟨j3CentTbl (k + 1), List.mem_toArray.2 hm, rfl⟩, fun i => ?_⟩
    beta_reduce
    rw [CFSG.KC.Census.SP.map_get _ _ (by rw [q16J3_size'.1]; exact hk' : k < q16J3G.size)]
    exact q16J3_gen hk' i

end CertificateChecks.KernelJ3Rank
