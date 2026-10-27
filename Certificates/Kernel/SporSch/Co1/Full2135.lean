
module

public import Certificates.Kernel.SporSch.Co1.Full2135Base

public import Certificates.Kernel.SporSch.Co1.FullK
public import Certificates.Kernel.SporSch.Co1.OrbX2
public import CFSG.Certificates.Kernel.SporSch.Co1FullSound
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.Co1StabFixBase1

public section

namespace CertificateChecks.KernelSporSch.Co1Full2135

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.SmallF2 Matrix
open CFSG.Sporadic.SmallF2.Native (transposeRows)
open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KS.SporSch.VOrb
open CertificateChecks.KernelSporSch.Co1Full CertificateChecks.KernelSporSch.Co1Orbs
open CertificateChecks.KernelSporSch.Co1Packed CertificateChecks.KernelSporSch.Co1Stab2148

local notation "Mt" g => ((g : GL24) : Matrix (Fin 24) (Fin 24) (ZMod 2))

theorem ge_Gw :
    8386560 ≤ Gw.ncard := by
  have h := count_bound stabH stabH_le_GA (fun h hh => stabH_fix_z hh) z_mem v3_mem
  have hf : (fib (toVecD 24 16120435)).ncard = 552 :=
    ncard_fib (by decide) (by decide) FW.hc0 FW.hcN FW.hc
  rw [ncard_X, ncard_kOrbit_stabH (k := 2) (by norm_num), w_eq, hf] at h
  have h2 : Native.stabSize 2 = 47104 := rfl
  rw [h2] at h
  change 8386560 ≤ (kOrbit GA (toVecD 24 16120435)).ncard
  omega

theorem ge_Gu :
    8292375 ≤ Gu.ncard := by
  have h := count_bound stabH stabH_le_GA (fun h hh => stabH_fix_z hh) z_mem v1_mem
  have hf : (fib (toVecD 24 10876918)).ncard = 552 :=
    ncard_fib (by decide) (by decide) FU.hc0 FU.hcN FU.hc
  rw [ncard_X, ncard_kOrbit_stabH (k := 1) (by norm_num), u_eq, hf] at h
  have h1 : Native.stabSize 1 = 46575 := rfl
  rw [h1] at h
  change 8292375 ≤ (kOrbit GA (toVecD 24 10876918)).ncard
  omega

theorem union_univ :
    O0 ∪ XS ∪ Gu ∪ Gw = Set.univ ∧ Gu.ncard = 8292375 ∧ Gw.ncard = 8386560 := by
  have d0X : Disjoint O0 XS := d0 (c := 2) (by decide) (by decide)
  have d0u : Disjoint O0 Gu := d0 (c := 10876918) (by decide) (by decide)
  have d0w : Disjoint O0 Gw := d0 (c := 16120435) (by decide) (by decide)
  have dXu : Disjoint XS Gu := (orbit_disj u_notin_X).symm
  have dXw : Disjoint XS Gw := (orbit_disj w_notin_X).symm
  have duw : Disjoint Gu Gw := (orbit_disj w_notin_Gu).symm
  have hcard : (O0 ∪ XS ∪ Gu ∪ Gw).ncard = O0.ncard + XS.ncard + Gu.ncard + Gw.ncard := by
    rw [Set.ncard_union_eq ((d0w.union_left dXw).union_left duw) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq (d0u.union_left dXu) (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq d0X (Set.toFinite _) (Set.toFinite _)]
  have hV : (Set.univ : Set Vec24).ncard = 2 ^ 24 := by
    rw [Set.ncard_univ, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : (O0 ∪ XS ∪ Gu ∪ Gw).ncard ≤ 2 ^ 24 := by
    rw [← hV]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have h0 : O0.ncard = 1 := Set.ncard_singleton 0
  have hu := ge_Gu
  have hw := ge_Gw
  rw [hcard, h0, ncard_X] at hle
  refine ⟨Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _), by omega,
    by omega⟩
  rw [hV, hcard, h0, ncard_X]
  omega

theorem mem_four
    (v : Vec24) : v ∈ O0 ∨ v ∈ XS ∨ v ∈ Gu ∨ v ∈ Gw := by
  have h : v ∈ O0 ∪ XS ∪ Gu ∪ Gw := by rw [union_univ.1]; exact Set.mem_univ v
  rcases h with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem root3 :
    kOrbit GA (toVecD 24 4096) = Gw := by
  have hq : q (toVecD 24 4096) = 1 := by rw [q_val, Nat.eq_of_beq_eq_true kq4096]; rfl
  rcases mem_four (toVecD 24 4096) with h | h | h | h
  · exact absurd h (notin_O0 (by decide) (by decide))
  · exact absurd (hq.symm.trans (q_X h)) q_one_ne
  · exact absurd (hq.symm.trans (q_Gu h)) q_one_ne
  · exact kOrbit_eq_of_mem h

theorem orbit_root3 :
    kOrbit GA (toVecD 24 (Native.fullRoot 3)) = Gw := root3

theorem root1 :
    kOrbit GA (toVecD 24 1) = Gu := by
  rcases mem_four (toVecD 24 1) with h | h | h | h
  · exact absurd h (notin_O0 (by decide) (by decide))
  · exact absurd ((memX (by decide)).mp h) (by rw [m1]; decide)
  · exact kOrbit_eq_of_mem h
  · have h1 := q_Gw h
    rw [q_val, Nat.eq_of_beq_eq_true kq1] at h1
    exact absurd h1 (by decide)

theorem orbit_root1 :
    kOrbit GA (toVecD 24 (Native.fullRoot 1)) = Gu := root1

theorem facts :
    (∀ v : Vec24, ∃ k < 4, v ∈ kOrbit GA (toVecD 24 (Native.fullRoot k))) ∧
    (∀ k < 4, (kOrbit GA (toVecD 24 (Native.fullRoot k))).ncard = Native.fullSize k) ∧
    (∀ k < 4, ∀ c < 2 ^ 24, toVecD 24 c ∈ kOrbit GA (toVecD 24 (Native.fullRoot k)) →
      Native.fullRoot k ≤ c) := by
  refine ⟨fun v => ?_, fun k hk => ?_, fun k hk c hc hmem => ?_⟩
  · rcases mem_four v with h | h | h | h
    · exact ⟨0, by norm_num, by rw [orbit_root0]; exact h⟩
    · exact ⟨2, by norm_num, by rw [orbit_root2]; exact h⟩
    · exact ⟨1, by norm_num, by rw [orbit_root1]; exact h⟩
    · exact ⟨3, by norm_num, by rw [orbit_root3]; exact h⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [orbit_root0]
      exact Set.ncard_singleton 0
    · rw [orbit_root1]
      exact union_univ.2.1
    · rw [orbit_root2]
      exact ncard_X
    · rw [orbit_root3]
      exact union_univ.2.2
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · exact Nat.zero_le c
    · rw [orbit_root1] at hmem
      change 1 ≤ c
      rcases Nat.eq_zero_or_pos c with rfl | h
      · rw [toVecD_zero] at hmem
        exact absurd hmem (zero_notin_orbit (c := 10876918) (by decide) (by decide))
      · exact h
    · rw [orbit_root2] at hmem
      exact notin_X_small hc hmem
    · rw [orbit_root3] at hmem
      change 4096 ≤ c
      by_contra hlt
      have h0 := q_Gw hmem
      rw [q_val, Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec klow c (by omega))] at h0
      exact absurd h0 (by decide)

end CertificateChecks.KernelSporSch.Co1Full2135

end
