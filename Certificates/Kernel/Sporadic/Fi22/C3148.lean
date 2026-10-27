
module

public import Certificates.Kernel.Sporadic.Fi22.F3148O0
public import Certificates.Kernel.Sporadic.Fi22.F3148O1
public import Certificates.Kernel.Sporadic.Fi22.F3148OZ
public import Certificates.Kernel.Sporadic.Fi22.C2068Base
public import Certificates.Kernel.Sporadic.Fi22.C3150
public import CFSG.Certificates.Kernel.SporSch.TranslateSearch

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22C3148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates.Native
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fi22F3148

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases e : a = b
  · subst e
    rw [Nat.beq_refl]
    exact beq_self_eq_true a
  · have h : Nat.beq a b = false := by
      cases h : Nat.beq a b
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) e
    rw [h]
    exact beq_false_of_ne e

theorem fixedList_unpack (P : Nat) : fixedList 3510 (unpack 3510 12 P) = fixL P := by
  unfold fixedList fixL
  refine List.filter_congr fun p hp => ?_
  rw [Fi22LabA.unpack_get' (List.mem_range.1 hp), beq_nat]

theorem gens_eq {G : Nat → Nat} (h : allN 2 (fun k => Nat.beq (G k) (Fi22PC.S k)) = true) :
    fi22OrigArrs.size = 2 ∧ ∀ k < 2, fi22OrigArrs[k]! = unpack 3510 12 (G k) := by
  refine ⟨by simp [fi22OrigArrs], fun k hk => ?_⟩
  have e : (fi22StrongArrs.extract 0 2)[k]! = fi22StrongArrs[k]! := by
    rw [getElem!_pos _ k (by simp [fi22StrongArrs]; omega),
      getElem!_pos fi22StrongArrs k (by simp [fi22StrongArrs]; omega)]
    simp
  rw [← Fi22C3147.orig_eq, e, Fi22X.bindsP.2.2.2.2.1 k (by omega),
    Nat.eq_of_beq_eq_true (allN_spec h k hk)]

theorem replay0 : SetReplayOK 3510 12 54 2 3511 3511 7 8 7 8 64 Fi22F3148O0.G Fi22F3148O0.GI
    (rowGet Fi22F3148O0.XT 676) (rowGet Fi22F3148O0.WT 40) (rowGet Fi22F3148O0.ST 20)
    (rowGet Fi22F3148O0.SIT 20) Fi22F3148O0.C (fixedList 3510 (fi22OuterStrong3510 6)[0]!) := by
  obtain ⟨c0, cN⟩ := by simpa only [bAnd_iff] using cnt0
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl _, by norm_num, by norm_num,
    by norm_num, by norm_num, fun k hk => allN_spec perm0 k hk, ?_, Fi22F3148O0.helt,
    Fi22F3148O0.hsrt, Nat.eq_of_beq_eq_true c0, Nat.eq_of_beq_eq_true cN, Fi22F3148O0.hrun⟩
  rw [Fi22LabA.out6_eq (by norm_num), fixedList_unpack]
  exact start0

theorem replay1 : SetReplayOK 3510 12 182 2 3511 3511 28 2 14 4 64 Fi22F3148O1.G Fi22F3148O1.GI
    (rowGet Fi22F3148O1.XT 2212) (rowGet Fi22F3148O1.WT 40) (rowGet Fi22F3148O1.ST 20)
    (rowGet Fi22F3148O1.SIT 20) Fi22F3148O1.C (fixedList 3510 (fi22OuterStrong3510 6)[1]!) := by
  obtain ⟨c0, cN⟩ := by simpa only [bAnd_iff] using cnt1
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl _, by norm_num, by norm_num,
    by norm_num, by norm_num, fun k hk => allN_spec perm1 k hk, ?_, Fi22F3148O1.helt,
    Fi22F3148O1.hsrt, Nat.eq_of_beq_eq_true c0, Nat.eq_of_beq_eq_true cN, Fi22F3148O1.hrun⟩
  rw [Fi22LabA.out6_eq (by norm_num), fixedList_unpack]
  exact start1

theorem replayZ : SetReplayOK 3510 12 694 2 3510 3510 55 1 28 2 64 Fi22F3148OZ.G Fi22F3148OZ.GI
    (rowGet Fi22F3148OZ.XT 8356) (rowGet Fi22F3148OZ.WT 40) (rowGet Fi22F3148OZ.ST 20)
    (rowGet Fi22F3148OZ.SIT 20) Fi22F3148OZ.C (fixedList 3510 (fi22OuterStrong3510 1)[0]!) := by
  obtain ⟨c0, cN⟩ := by simpa only [bAnd_iff] using cntZ
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl _, by norm_num, by norm_num,
    by norm_num, by norm_num, fun k hk => allN_spec permZ k hk, ?_, Fi22F3148OZ.helt,
    Fi22F3148OZ.hsrt, Nat.eq_of_beq_eq_true c0, Nat.eq_of_beq_eq_true cN, Fi22F3148OZ.hrun⟩
  rw [Fi22E2073.outE, fixedList_unpack]
  exact startZ

theorem facts : ((fi22OuterStrong3510 1)[0]!)[0]! = 0 ∧
    (∀ k < 3, eqA 3510 (compA 3510 (fi22OuterStrong3510 1)[0]! (fi22OuterStrong3510 3)[k]!)
      (compA 3510 (fi22OuterStrong3510 3)[k]! (fi22OuterStrong3510 1)[0]!) = true) ∧
    translatesOK fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 6)[0]!) fi22FixOrbit0.1
      fi22FixOrbit0.2.1 fi22FixOrbit0.2.2 = true ∧
    fi22FixOrbit0.1.toList.Nodup ∧ fi22FixOrbit0.1.size = 3511 ∧
    translatesOK fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 6)[1]!) fi22FixOrbit1.1
      fi22FixOrbit1.2.1 fi22FixOrbit1.2.2 = true ∧
    fi22FixOrbit1.1.toList.Nodup ∧ fi22FixOrbit1.1.size = 3511 ∧
    translatesOK fi22OrigArrs (fixedList 3510 (fi22OuterStrong3510 1)[0]!) fi22FixOrbitZ.1
      fi22FixOrbitZ.2.1 fi22FixOrbitZ.2.2 = true ∧
    fi22FixOrbitZ.1.toList.Nodup ∧ fi22FixOrbitZ.1.size = 3510 := by
  obtain ⟨z0, cE, hM⟩ := by simpa only [bAnd_iff] using zFix
  obtain ⟨a0, b0, d0⟩ := SRP.translateReplay_proved (gens_eq gens0) replay0
  obtain ⟨a1, b1, d1⟩ := SRP.translateReplay_proved (gens_eq gens1) replay1
  obtain ⟨aZ, bZ, dZ⟩ := SRP.translateReplay_proved (gens_eq gensZ) replayZ
  refine ⟨?_, fun k hk => ?_, a0, b0, d0, a1, b1, d1, aZ, bZ, dZ⟩
  · rw [Fi22E2073.outE, Fi22LabA.unpack_get' (by norm_num)]
    exact Nat.eq_of_beq_eq_true z0
  · obtain ⟨cM, hc⟩ := (bAnd_iff _ _).1 (allN_spec hM k hk)
    rw [Fi22E2073.outE, Fi22C3150.outM_eq (by omega), Fi22X.comp_eq cE cM, Fi22X.comp_eq cM cE]
    exact Fi22X.eqA_of (Fi22X.cn_c cE cM) (Fi22X.cn_c cM cE) hc

end CertificateChecks.KernelSpor.Fi22C3148

end
