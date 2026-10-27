module

public import Certificates.Kernel.Q16J2.Checks
public import CFSG.Certificates.Kernel.Q16Q16KSound
public import CFSG.Certificates.Kernel.Q16Q16KRes
public import CFSG.Certificates.Kernel.Census.E16Sound
import all Certificates.Kernel.Q16J2.Checks

public section

namespace CertificateChecks.KernelQ16J2

open CFSG.KC.Q16Q16K CFSG.KC.Census CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
open CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.ComponentClassification.J2Cover

theorem q16J2_free : q16J2R.all (chkX 16 4 q16J2R) = true := by
  have h := all_drop_chunk (a := 0) (B := 32) (allL_eq_all _ _ ▸ q16J2F0)
    (all_drop_chunk (a := 32) (B := 32) (allL_eq_all _ _ ▸ q16J2F1)
    (all_drop_chunk (a := 64) (B := 32) (allL_eq_all _ _ ▸ q16J2F2)
    (all_drop_chunk (a := 96) (B := 32) (allL_eq_all _ _ ▸ q16J2F3)
    (all_drop_chunk (a := 128) (B := 32) (allL_eq_all _ _ ▸ q16J2F4)
    (all_drop_chunk (a := 160) (B := 32) (allL_eq_all _ _ ▸ q16J2F5)
    (all_drop_chunk (a := 192) (B := 32) (allL_eq_all _ _ ▸ q16J2F6)
      (allL_eq_all _ _ ▸ q16J2F7)))))))
  rw [List.drop_zero] at h
  exact h

theorem q16J2_res :
    Nat.card ↥(Subgroup.closure (permsA 16 (q16J2G.map (unpackP 16 4)))) = 2 ^ 8 ∧
      NoQ16Q16 ↥(Subgroup.closure (permsA 16 (q16J2G.map (unpackP 16 4)))) := by
  obtain ⟨hg, hc, hps⟩ := q16J2_canon
  have hpts : q16J2C.pts.toList = q16J2R.map Prod.fst := by
    rw [q16J2R, List.map_map]
    exact ((List.map_congr_left fun _ _ => rfl).trans (List.map_id _)).symm
  have hrec : q16J2R.all (recOK 16 4) = true := by
    rw [q16J2R, List.all_map, List.all_eq_true]
    intro x hx
    exact recOK_mkRec (List.all_eq_true.1 hc x hx)
  obtain ⟨h1, h2⟩ := q16K_sound (by norm_num) (by norm_num)
    (fun p hp => Nat.blt_eq.mp (List.all_eq_true.1 hps p hp)) hg hpts hrec q16J2_enum q16J2_free
  refine ⟨?_, h2⟩
  rw [h1, q16J2R, List.length_map, Array.length_toList]
  decide +kernel

theorem q16J2_noQ16Q16 : NoQ16Q16 ↥sylowS := by
  have hG3 : q16J2G.size = 3 := Nat.eq_of_beq_eq_true q16J2_size.1
  have hO16 : q16J2O.size = 16 := Nat.eq_of_beq_eq_true q16J2_size.2
  have hpt : ∀ k < 3, ∀ q < 16, q16J2O[q]! < 315 ∧
      (sylowStrong[k]!)[q16J2O[q]!]! = q16J2O[at' 4 q16J2G[k]! q]! := by
    intro k hk q hq
    have h := List.all_eq_true.1 (List.all_eq_true.1 q16J2_bind k (List.mem_range.2 hk)) q
      (List.mem_range.2 hq)
    simp only [Bool.and_eq_true] at h
    exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩
  let O : Fin 16 → Fin 315 := fun q => ⟨q16J2O[q.val]!, (hpt 0 (by norm_num) q q.2).1⟩
  have hO : Function.Injective O := by
    intro a b hab
    have e : q16J2O[a.val]! = q16J2O[b.val]! := congrArg Fin.val hab
    rw [getElem!_pos q16J2O a.val (by omega), getElem!_pos q16J2O b.val (by omega)] at e
    have e' : q16J2O.toList[a.val]'(by simp; omega) = q16J2O.toList[b.val]'(by simp; omega) := by
      simpa using e
    exact Fin.ext ((List.Nodup.getElem_inj_iff q16J2_nodup).1 e')
  have hcan : ∀ k < 3, canon1 16 4 q16J2G[k]! = true := fun k hk => by
    rw [getElem!_pos q16J2G k (by omega)]
    exact List.all_eq_true.1 q16J2_canon.1 _ (Array.getElem_mem_toList (by omega))
  have hgen : ∀ k < 3, ∀ i : Fin 16, permOfArr 315 sylowStrong[k]! (O i) =
      O (permOfArr 16 (unpackP 16 4 q16J2G[k]!) i) := by
    intro k hk i
    have hr := rep_permOfArr_of_chainOK sylowChain_ok (j := k) (by
      have : sylowStrong.size = 5 := rfl
      omega)
    have hv : validA 16 (unpackP 16 4 q16J2G[k]!) = true := by
      rw [SP.validA_unpack (by norm_num) (hcan k hk)]
      exact pvalid_of_penumOK q16J2_enum (by omega)
    have hs := rep_of_validA hv i
    rw [SP.unpackP_get_canon (hcan k hk)] at hs
    apply Fin.ext
    rw [← hr (O i)]
    change (sylowStrong[k]!)[q16J2O[i.val]!]! = q16J2O[(permOfArr 16 _ i).val]!
    rw [← hs]
    exact (hpt k hk i i.2).2
  have hc := card_sylowS
  rw [sylowS, sylowChain, ofArrays_originalSubgroup] at hc ⊢
  obtain ⟨hcard, hno⟩ := q16J2_res
  refine noQ16Q16_of_res O hO ?_ ?_ (hc.le.trans hcard.ge) hno
  · rintro g ⟨k, hk, rfl⟩ i
    exact ⟨_, hgen k hk i⟩
  · rintro σ ⟨k, hk, rfl⟩
    have hk' : k < 3 := by
      have : k < (q16J2G.map (unpackP 16 4)).size := hk
      rw [Array.size_map] at this
      omega
    refine ⟨_, ⟨k, hk', rfl⟩, fun i => ?_⟩
    beta_reduce
    rw [SP.map_get _ _ (by omega : k < q16J2G.size)]
    exact hgen k hk' i

end CertificateChecks.KernelQ16J2
