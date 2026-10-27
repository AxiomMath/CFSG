module

public import Certificates.Kernel.HNMult.Facts
public import CFSG.Certificates.Kernel.LaneChainSound
public import Certificates.Kernel.HNMult.Chain
import all Certificates.Kernel.HNMult.Facts
import Certificates.Kernel.HNMult.ChecksK
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHNMult

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KD.HNMult CFSG.KS.LaneChain CFSG.Sporadic.F5

local notation "Dt" => CFSG.Sporadic.HN.Native.hnData

noncomputable abbrev H5 : Subgroup (J Dt) := Subgroup.closure (Set.range fun i : Fin 5 => gf i.val)

theorem rootsOK_vld {RB : Nat → Nat} {vld : Nat → Bool} {lo : Nat} : ∀ m,
    rootsOK RB vld lo m = true → ∀ i, lo ≤ i → i < m → vld (RB i) = true
  | 0, _, i, _, h => absurd h (Nat.not_lt_zero i)
  | m + 1, h, i, hl, hi => by
    have h' : andB (rootsOK RB vld lo m)
        (Bool.rec (motive := fun _ => Bool) true (vld (RB m)) (Nat.ble lo m)) = true := h
    obtain ⟨h1, h2⟩ := andT h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact rootsOK_vld m h1 i hl hi
    · have hb : Nat.ble lo i = true := Nat.ble_eq.mpr hl
      rw [hb] at h2
      exact h2

theorem invs_vld_aux {RB : Nat → Nat} {mul : Nat → Nat → Nat} {vld : Nat → Bool} {L ONE : Nat} :
    ∀ m, Nat.rec (motive := fun _ => Bool) true (fun g ih => andB ih
      (andB (vld (RB (Nat.add (Nat.succ L) g)))
        (Nat.beq (mul (RB (Nat.succ g)) (RB (Nat.add (Nat.succ L) g))) ONE))) m = true →
      ∀ g < m, vld (RB (Nat.add (Nat.succ L) g)) = true
  | 0, _, g, h => absurd h (Nat.not_lt_zero g)
  | m + 1, h, g, hg => by
    obtain ⟨h1, h2⟩ := andT h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hg with hg | rfl
    · exact invs_vld_aux m h1 g hg
    · exact (andT h2).1

theorem invs_vld {RB : Nat → Nat} {mul : Nat → Nat → Nat} {vld : Nat → Bool} {L ONE : Nat}
    (h : invsOK RB mul vld L ONE = true) : ∀ g < L, vld (RB (Nat.add (Nat.succ L) g)) = true := by
  unfold invsOK at h
  exact invs_vld_aux L h

theorem good_gen (i : ℕ) (hi : i < 5) :
    Good matHom H5 13 1729 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (RB (i + 7)) := by
  unfold Good
  have h1 : 1 ≤ i + 7 := by omega
  have h14 : i + 7 < 14 := by omega
  refine ⟨rootsOK_vld 14 hroots (i + 7) h1 h14, gf i,
    Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩, ?_⟩
  have h := mat_gf i (by omega)
  rw [mat_eq] at h
  rw [h]
  unfold Mr
  have e : i + 7 = 6 + i + 1 := by omega
  rw [e]

theorem good_inv (i : ℕ) (hi : i < 5) :
    Good matHom H5 13 1729 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H (RB (i + 20)) := by
  have h13 : 6 + i < 13 := by omega
  have hv := invs_vld hinv (6 + i) h13
  have e1 : Nat.add (Nat.succ 13) (6 + i) = i + 20 := by
    change 14 + (6 + i) = i + 20
    omega
  rw [e1] at hv
  unfold Good
  refine ⟨hv, (gf i)⁻¹, Subgroup.inv_mem _ (Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩), ?_⟩
  have h := mat_inv_of (x := gf i) (g := 6 + i) (by omega) (mat_gf i (by omega))
  rw [mat_eq] at h
  rw [h]
  unfold Mi
  have e : i + 20 = 14 + (6 + i) := by omega
  rw [e]

theorem allGood_M₀ : AllGood matHom H5 13 1729 229957 CFSG.KD.FamHNSeed.L CFSG.KD.FamHNSeed.H
    CFSG.KD.HNMChain.M₀ := by
  intro r hr
  have h10 : CFSG.KD.HNMChain.M₀.length = 10 := rfl
  rw [h10] at hr ⊢
  interval_cases r
  · exact good_gen 0 (by norm_num)
  · exact good_gen 1 (by norm_num)
  · exact good_gen 2 (by norm_num)
  · exact good_gen 3 (by norm_num)
  · exact good_gen 4 (by norm_num)
  · exact good_inv 0 (by norm_num)
  · exact good_inv 1 (by norm_num)
  · exact good_inv 2 (by norm_num)
  · exact good_inv 3 (by norm_num)
  · exact good_inv 4 (by norm_num)

theorem card_closure_ge : 88704000 ≤ Nat.card H5 :=
  card_ge_of_chainOK matHom H5 CFSG.KD.FamHNSeed.consts rfl allGood_M₀ CFSG.KD.HNMChain.chain_ok

end CertificateChecks.KernelHNMult

end
