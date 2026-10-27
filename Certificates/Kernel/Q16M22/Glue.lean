module

public import Certificates.Kernel.Q16M22.Checks
public import Certificates.Kernel.Census.M22II.Bind
public import Certificates.Kernel.Census.M22II.T
public import CFSG.Certificates.Kernel.Q16Q16KSound
public import CFSG.Certificates.Kernel.Census.E16Sound
import all Certificates.Kernel.Q16M22.Checks

public section

namespace CertificateChecks.KernelQ16M22

open CFSG.KC.Q16Q16K CFSG.KC.Census CertificateChecks.KernelCensus.M22II
open CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.RankThree.Native
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

@[expose] noncomputable def m22S : Subgroup (Equiv.Perm (Fin 24)) :=
  Subgroup.closure (permsA 24 (m22IISG.map (unpackP 24 5)))

theorem q16M22_canon : m22IISG.toList.all (canon1 24 5) = true ∧
    m22IICS.pts.toList.all (canon1 24 5) = true := by
  have h := kCanon
  simp only [canonP, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.2⟩

theorem q16M22_free : q16M22R.all (chkX 24 5 q16M22R) = true := by
  have h := all_drop_chunk (a := 0) (B := 32) (allL_eq_all _ _ ▸ q16M22F0)
    (all_drop_chunk (a := 32) (B := 32) (allL_eq_all _ _ ▸ q16M22F1)
    (all_drop_chunk (a := 64) (B := 32) (allL_eq_all _ _ ▸ q16M22F2)
    (all_drop_chunk (a := 96) (B := 32) (allL_eq_all _ _ ▸ q16M22F3)
    (all_drop_chunk (a := 128) (B := 32) (allL_eq_all _ _ ▸ q16M22F4)
    (all_drop_chunk (a := 160) (B := 32) (allL_eq_all _ _ ▸ q16M22F5)
    (all_drop_chunk (a := 192) (B := 32) (allL_eq_all _ _ ▸ q16M22F6)
      (allL_eq_all _ _ ▸ q16M22F7)))))))
  rw [List.drop_zero] at h
  exact h

theorem q16M22_card_noQ16Q16 : Nat.card ↥m22S = 2 ^ 8 ∧ NoQ16Q16 ↥m22S := by
  obtain ⟨hg, hc⟩ := q16M22_canon
  have hpts : m22IICS.pts.toList = q16M22R.map Prod.fst := by
    rw [q16M22R, List.map_map]
    exact ((List.map_congr_left fun _ _ => rfl).trans (List.map_id _)).symm
  have hrec : q16M22R.all (recOK 24 5) = true := by
    rw [q16M22R, List.all_map, List.all_eq_true]
    intro x hx
    exact recOK_mkRec (List.all_eq_true.1 hc x hx)
  obtain ⟨h1, h2⟩ := q16K_sound (by norm_num) (by norm_num) (by decide) hg hpts hrec kS
    q16M22_free
  refine ⟨?_, h2⟩
  unfold m22S
  rw [h1, q16M22R, List.length_map, Array.length_toList]
  decide +kernel

theorem q16M22_le_range : m22S ≤ iota.range := by
  rw [m22S, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact mem_range_of_pairA (CFSG.Monster.B.Co2.allLt_spec kGen hk)

end CertificateChecks.KernelQ16M22
