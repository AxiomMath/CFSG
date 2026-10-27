module

public import Certificates.Kernel.Q16J3.Checks
public import Certificates.Kernel.Q16J3.Bind
public import CFSG.Certificates.Kernel.Q16Q16KSound
public import CFSG.Certificates.Kernel.Q16Q16KRes
public import CFSG.Certificates.Kernel.Census.E16Sound
import all Certificates.Kernel.Q16J3.Checks

public section

namespace CertificateChecks.KernelQ16J3

open CFSG.KC.Q16Q16K CFSG.KC.Census CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
open CFSG.RankThree.Native CFSG.Sporadic.SmallOddCore CertificateChecks.KernelSpor.OddCore

theorem q16J3_free : q16J3R.all (chkX 32 5 q16J3R) = true := by
  have h := all_drop_chunk (a := 0) (B := 32) (allL_eq_all _ _ ▸ q16J3F0)
    (all_drop_chunk (a := 32) (B := 32) (allL_eq_all _ _ ▸ q16J3F1)
    (all_drop_chunk (a := 64) (B := 32) (allL_eq_all _ _ ▸ q16J3F2)
    (all_drop_chunk (a := 96) (B := 32) (allL_eq_all _ _ ▸ q16J3F3)
    (all_drop_chunk (a := 128) (B := 32) (allL_eq_all _ _ ▸ q16J3F4)
    (all_drop_chunk (a := 160) (B := 32) (allL_eq_all _ _ ▸ q16J3F5)
    (all_drop_chunk (a := 192) (B := 32) (allL_eq_all _ _ ▸ q16J3F6)
      (allL_eq_all _ _ ▸ q16J3F7)))))))
  rw [List.drop_zero] at h
  exact h

theorem q16J3_res :
    Nat.card ↥(Subgroup.closure (permsA 32 (q16J3G.map (unpackP 32 5)))) = 2 ^ 8 ∧
      NoQ16Q16 ↥(Subgroup.closure (permsA 32 (q16J3G.map (unpackP 32 5)))) := by
  obtain ⟨hg, hc, hps⟩ := q16J3_canon
  have hpts : q16J3C.pts.toList = q16J3R.map Prod.fst := by
    rw [q16J3R, List.map_map]
    exact ((List.map_congr_left fun _ _ => rfl).trans (List.map_id _)).symm
  have hrec : q16J3R.all (recOK 32 5) = true := by
    rw [q16J3R, List.all_map, List.all_eq_true]
    intro x hx
    exact recOK_mkRec (List.all_eq_true.1 hc x hx)
  obtain ⟨h1, h2⟩ := q16K_sound (by norm_num) (by norm_num)
    (fun p hp => Nat.blt_eq.mp (List.all_eq_true.1 hps p hp)) hg hpts hrec q16J3_enum q16J3_free
  refine ⟨?_, h2⟩
  rw [h1, q16J3R, List.length_map, Array.length_toList]
  decide +kernel

theorem q16J3_tbls : j3SylowGenTbls = (List.range 8).map fun i => j3CentTbl (i + 1) := by
  unfold j3SylowGenTbls
  rfl

theorem q16J3_size' : q16J3G.size = 8 ∧ q16J3O.size = 32 :=
  ⟨Nat.eq_of_beq_eq_true q16J3_size.1, Nat.eq_of_beq_eq_true q16J3_size.2⟩

theorem q16J3_pt {k : Nat} (hk : k < 8) {q : Nat} (hq : q < 32) : q16J3O[q]! < 6156 ∧
    at' 13 (CertificateChecks.KernelSpor.J3CentP (k + 1)) q16J3O[q]! =
      q16J3O[at' 5 q16J3G[k]! q]! := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 q16J3_bind k (List.mem_range.2 hk)) q
    (List.mem_range.2 hq)
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

@[expose] noncomputable def q16J3Pt (q : Fin 32) : Fin 6156 :=
  ⟨q16J3O[q.val]!, (q16J3_pt (k := 0) (by norm_num) q.2).1⟩

theorem q16J3Pt_injective : Function.Injective q16J3Pt := by
  intro a b hab
  have e : q16J3O[a.val]! = q16J3O[b.val]! := congrArg Fin.val hab
  have hO32 := q16J3_size'.2
  rw [getElem!_pos q16J3O a.val (by omega), getElem!_pos q16J3O b.val (by omega)] at e
  have e' : q16J3O.toList[a.val]'(by simp; omega) = q16J3O.toList[b.val]'(by simp; omega) := by
    simpa using e
  exact Fin.ext ((List.Nodup.getElem_inj_iff q16J3_nodup).1 e')

theorem q16J3_gen {k : Nat} (hk : k < 8) (i : Fin 32) :
    tp 6156 (j3CentTbl (k + 1)) (q16J3Pt i) =
      q16J3Pt (CFSG.Monster.B.Co2.permOfArr 32 (unpackP 32 5 q16J3G[k]!) i) := by
  have hG8 := q16J3_size'.1
  have hcan : canon1 32 5 q16J3G[k]! = true := by
    rw [getElem!_pos q16J3G k (by omega)]
    exact List.all_eq_true.1 q16J3_canon.1 _ (Array.getElem_mem_toList (by omega))
  have hp : CFSG.Sporadic.SmallOddCore.permOK 6156 (j3CentTbl (k + 1)) = true :=
    List.all_eq_true.1 j3_permOK_all (k + 1) (List.mem_range.2 (by omega))
  have hr := co2Rep_natArr_iff.2 (rep_tp hp) (q16J3Pt i)
  have hl : (Native.natArr (j3CentTbl (k + 1)))[(q16J3Pt i).val]! =
      at' 13 (CertificateChecks.KernelSpor.J3CentP (k + 1)) (q16J3Pt i).val := by
    rw [j3CentTbl_eq (by omega)]
    exact CFSG.Monster.B.Co2.getElem!_ofFn_nat _ (q16J3Pt i).2
  have hv : validA 32 (unpackP 32 5 q16J3G[k]!) = true := by
    rw [SP.validA_unpack (by norm_num) hcan]
    exact pvalid_of_penumOK q16J3_enum (by omega)
  have hs := rep_of_validA hv i
  rw [SP.unpackP_get_canon hcan] at hs
  apply Fin.ext
  rw [← hr, hl]
  change at' 13 (CertificateChecks.KernelSpor.J3CentP (k + 1)) q16J3O[i.val]! =
    q16J3O[(CFSG.Monster.B.Co2.permOfArr 32 _ i).val]!
  rw [← hs]
  exact (q16J3_pt hk i.2).2

theorem q16J3_noQ16Q16 :
    NoQ16Q16 ↥j3S := by
  have hc : Nat.card ↥j3S = 256 := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial.2.1
  rw [j3S] at hc ⊢
  obtain ⟨hcard, hno⟩ := q16J3_res
  refine noQ16Q16_of_res q16J3Pt q16J3Pt_injective ?_ ?_ (hc.le.trans hcard.ge) hno
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
    rw [SP.map_get _ _ (by rw [q16J3_size'.1]; exact hk' : k < q16J3G.size)]
    exact q16J3_gen hk' i

end CertificateChecks.KernelQ16J3
