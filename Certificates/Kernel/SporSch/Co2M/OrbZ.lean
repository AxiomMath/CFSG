module

public import Certificates.Kernel.SporSch.Co2M.OrbZ0
public import Certificates.Kernel.SporSch.Co2M.OrbZ1
public import Certificates.Kernel.SporSch.Co2M.OrbZ2
public import Certificates.Kernel.SporSch.Co2M.OrbZ3
public import Certificates.Kernel.SporSch.Co2M.OrbZ4
public import Certificates.Kernel.SporSch.Co2M.OrbZ5
public import Certificates.Kernel.SporSch.Co2M.OrbZ6
public import Certificates.Kernel.SporSch.Co2M.OrbZ7
public import CFSG.Certificates.Kernel.SporSch.SetTreeSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2M CFSG.KS.SporSch CFSG.KS.SporSch.Co2SFix
open CFSG.KS.SporSch.KeySearch CFSG.KS.MatRep CFSG.RankThree.Native.F2
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Schreier.Co3 CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native CFSG.KS.SporSch.SetTree CFSG.Sporadic.Co2Cert

theorem oz_all : ∀ i < 56925, ozK i = true := by
  have h8 : ∀ q < 8, ∀ t < 7168, ozK (Nat.add (7168 * q) t) = true := by
    intro q hq
    interval_cases q
    exacts [oz0, oz1, oz2, oz3, oz4, oz5, oz6, oz7]
  intro i hi
  have h := h8 (i / 7168) (by omega) (i % 7168) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (7168 * (i / 7168)) (i % 7168) = i := Nat.div_add_mod i 7168
  rwa [e] at h

theorem oz_parts {i : Nat} (hi : i < 56925) :
    eltK 2300 12 284 (OZX i) = true ∧ treeK 12 284 Co2OZ.G OZX 2 i = true ∧
      sortMK 12 284 OZX OZS 56925 i = true := by
  have h := oz_all i hi
  unfold ozK at h
  have hb : Nat.blt i 56925 = true := by rwa [Nat.blt_eq]
  rw [hb] at h
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 h
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
  rw [CFSG.KS.SporSch.SetTree.strictB_eq'] at a
  exact ⟨a, b, c⟩

theorem aArrs_size' : aArrs.size = 2 := by rw [aRep.1]; rfl

theorem aArrs_perm' : ∀ k < aArrs.size, KeySearch.PermA 2300 aArrs[k]! := by
  intro k hk
  have h := repT_get aRep (by rw [← aRep.1]; exact hk)
  have hi := isInvA_permOfMat good.hd good.nodup good.lt h.2
  rw [← h.1, V_size, isInvA, CFSG.Monster.B.Co2.allLt_iff] at hi
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_⟩
  · have := hi x hx
    rw [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  · have h1 := hi x hx
    have h2 := hi y hy
    rw [Bool.and_eq_true, beq_iff_eq] at h1 h2
    rw [← h1.2, ← h2.2, e]

theorem iz_good : KeySearch.Good 2300 co2IzNat := by
  unfold KeySearch.Good
  decide +kernel

theorem iz_eq : izList = co2IzNat := by
  have hf := fix_ok
  rw [beq_iff_eq] at hf
  rw [← hf]
  unfold izList fixedList
  refine List.filter_congr fun p hp => ?_
  have hp' := List.mem_range.1 hp
  have hpV : p < co2PackedVecs.size := by rw [V_size]; exact hp'
  rw [zRep.1, permOfMat_get hpV, vmK_eq, ← V_get hp']
  have hm := zRep.2.1 _ (mem_of_lt hpV)
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]
  constructor
  · intro h
    rw [← (getElem_vidx hm).2, h]
  · intro h
    rw [h, vidx_get good.nodup hpV]

theorem record : orbitRecordOK izList 56925 (co3KeySearch aArrs izList 56925) = true := by
  rw [iz_eq]
  obtain ⟨h1, h2, h3⟩ := keySearch_spec (n := 2300) (bound := 56925) (by norm_num) aArrs_perm'
    iz_good
  have hg : ∀ k < 2, aArrs[k]! = unpack 2300 12 (Co2OZ.G k) := fun k hk => by
    rw [aArrs_get hk, Nat.eq_of_beq_eq_true (allN_spec gens_ok k hk)]
  have hsz := h3 (setTree_bound (n := 2300) (w := 12) (s := 284) (kg := 2) (c := 56925)
    (G := Co2OZ.G) (X := OZX) (SO := OZS) aArrs_size' hg
    (fun k hk => aArrs_perm' k (by rw [aArrs_size']; exact hk)) (by norm_num) (by norm_num)
    (fun i hi => (oz_parts hi).1) start_ok (fun i hi => (oz_parts hi).2.1)
    (fun i hi => (oz_parts hi).2.2))
  unfold orbitRecordOK
  rw [h1, h2, hsz]
  rfl

theorem iz_length : izList.length = 284 := by
  rw [iz_eq]
  rfl

end CertificateChecks.KernelSporSch.Co2M

end
