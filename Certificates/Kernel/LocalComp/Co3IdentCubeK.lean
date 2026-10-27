module

public import Certificates.Kernel.LocalComp.Co3IdentFactsK
public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Co3IdentCubeInputs
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Co3Id

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Fendel CFSG.KC.Co3Bfs
open CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.SympSix.Co3Ident CFSG.Sporadic.Schreier.Co3
open CFSG.Sporadic.Schreier.Co3.Native CertificateChecks.KernelLC CertificateChecks.KernelSpor

@[expose] def CL : List Nat :=
  [0, 4, 8, 12, 38, 45, 71, 103, 150, 278, 328, 389, 453, 485, 661, 696, 803, 813, 828, 916, 934,
    1022, 1032, 1126, 1172, 1195, 1243, 1350, 1352, 1376, 1397, 1555, 1687, 1710, 1744, 1788,
    1804, 1854, 1859, 1947, 2016, 2100, 2132, 2138, 2170, 2181, 2345, 2363, 2368, 2373, 2474,
    2500, 2518, 2523, 2611, 2613, 2690, 2743, 2751, 2801, 2812, 2844, 2852, 2879, 2906, 2917,
    3026, 3117, 3146, 3190, 3198, 3237, 3247, 3251, 3259, 3351, 3371, 3422, 3426, 3455, 3457,
    3475, 3524, 3527, 3529, 3570, 3590, 3617, 3625, 3644, 3649, 3655, 3703, 3715, 3729, 3754,
    3765, 3792, 3827, 3838, 3910, 3995, 3999, 4023, 4061, 4113, 4136, 4143, 4148, 4195, 4197,
    4263, 4273, 4313, 4346, 4361, 4389, 4399, 4411, 4430, 4431, 4433, 4435, 4479, 4510, 4555,
    4581, 4607]

theorem CL_lt : ∀ i ∈ CL, i < 4608 := by decide

@[expose] noncomputable def memOK (i : Nat) : Bool := cy (HR.E i) == CL.contains i

@[expose] noncomputable def kMemF (k : Nat) : Bool := allFrom (512 * k) 512 memOK

#kc_each_unfold kMemF 0 9 as CertificateChecks.KernelLC.Co3Id.kMem

#kc_forall_chunks kMem_all (fun k => allFrom (512 * k) 512 memOK = true) 9
  CertificateChecks.KernelLC.Co3Id.kMem 1

theorem mem_all (i : Nat) (hi : i < 4608) : cy (HR.E i) = CL.contains i := by
  have h : memOK i = true :=
    blocks (B := 512) (nb := 9) (by omega) (fun k hk => kMem_all k hk) i (by omega)
  unfold memOK at h
  simpa using h

@[expose] noncomputable def RK (i j : Nat) : Bool :=
  Nat.beq (pc KPP (pc (HR.E i) (pc KPP (HR.E j)))) (pc (HR.E j) (HR.E i))

@[expose] noncomputable def UK (j : Nat) : Bool := Nat.beq (pc UP (HR.E j)) (pc (HR.E j) UP)

@[expose] noncomputable def cubeOK (j : Nat) : Bool :=
  (CL.all (fun i => RK i j) && UK j) == (Nat.beq (HR.E j) KPP || Nat.beq (HR.E j) KPCP)

@[expose] noncomputable def kCubeF (k : Nat) : Bool := allFrom (2 * k) 2 (fun m => cubeOK (CL.getD m 0))

#kc_each_unfold kCubeF 0 64 as CertificateChecks.KernelLC.Co3Id.kCube

#kc_forall_chunks kCube_all (fun k => allFrom (2 * k) 2 (fun m => cubeOK (CL.getD m 0)) = true) 64
  CertificateChecks.KernelLC.Co3Id.kCube 1

theorem cube_pos (m : Nat) (hm : m < 128) : cubeOK (CL.getD m 0) = true :=
  blocks (f := fun m => cubeOK (CL.getD m 0)) (B := 2) (nb := 64) (by omega)
    (fun k hk => kCube_all k hk) m (by omega)

theorem CL_length : CL.length = 128 := rfl

theorem cube_mem (j : Nat) (hj : j ∈ CL) : cubeOK j = true := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hj
  have := cube_pos m (by rw [CL_length] at hm; exact hm)
  rwa [List.getD_eq_getElem _ _ hm] at this

theorem hcomm (i : Nat) (hi : i < 4608) : commutesA 276 hList[i]! yArr = cy (HR.E i) := by
  rw [hList_get i hi, y_eq, comm_unpack (cHR i hi) cY]
  rfl

theorem hR (i j : Nat) (hi : i < 4608) (hj : j < 4608) :
    eqA 276 (compA 276 kpArr (compA 276 hList[i]! (compA 276 kpArr hList[j]!)))
      (compA 276 hList[j]! hList[i]!) = RK i j := by
  have ci := cHR i hi
  have cj := cHR j hj
  rw [hList_get i hi, hList_get j hj, kp_eq, compA_unpack cKP cj,
    compA_unpack ci (canon_pc cKP cj), compA_unpack cKP (canon_pc ci (canon_pc cKP cj)),
    compA_unpack cj ci, eqA_unpack (canon_pc cKP (canon_pc ci (canon_pc cKP cj))) (canon_pc cj ci)]
  rfl

theorem hU (j : Nat) (hj : j < 4608) :
    eqA 276 (compA 276 uArr hList[j]!) (compA 276 hList[j]! uArr) = UK j := by
  have cj := cHR j hj
  rw [hList_get j hj, u_eq, compA_unpack cU cj, compA_unpack cj cU,
    eqA_unpack (canon_pc cU cj) (canon_pc cj cU)]
  rfl

theorem hr (j : Nat) (hj : j < 4608) :
    (eqA 276 hList[j]! kpArr || eqA 276 hList[j]! kpcArr) =
      (Nat.beq (HR.E j) KPP || Nat.beq (HR.E j) KPCP) := by
  have cj := cHR j hj
  rw [hList_get j hj, kp_eq, kpc_eq, eqA_unpack cj cKP, eqA_unpack cj cKPC]

theorem facts3095 : ∀ j < 4608, commutesA 276 hList[j]! yArr = true →
    ((allLt 4608 fun i => !commutesA 276 hList[i]! yArr ||
      eqA 276 (compA 276 kpArr (compA 276 hList[i]! (compA 276 kpArr hList[j]!)))
        (compA 276 hList[j]! hList[i]!)) &&
      eqA 276 (compA 276 uArr hList[j]!) (compA 276 hList[j]! uArr)) =
    (eqA 276 hList[j]! kpArr || eqA 276 hList[j]! kpcArr) := by
  intro j hj hcj
  have hjm : j ∈ CL := by
    rw [hcomm j hj, mem_all j hj] at hcj
    exact List.contains_iff_mem.1 hcj
  have hall : (allLt 4608 fun i => !commutesA 276 hList[i]! yArr ||
      eqA 276 (compA 276 kpArr (compA 276 hList[i]! (compA 276 kpArr hList[j]!)))
        (compA 276 hList[j]! hList[i]!)) = CL.all (fun i => RK i j) := by
    rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, List.all_eq_true]
    constructor
    · intro h i hi
      have hi' := CL_lt i hi
      have := h i hi'
      rw [hcomm i hi', mem_all i hi', List.contains_iff_mem.2 hi, hR i j hi' hj] at this
      simpa using this
    · intro h i hi
      rw [hcomm i hi, mem_all i hi, hR i j hi hj]
      by_cases hm : i ∈ CL
      · rw [List.contains_iff_mem.2 hm, h i hm]
        rfl
      · have : CL.contains i = false := by
          rw [Bool.eq_false_iff]
          intro hc
          exact hm (List.contains_iff_mem.1 hc)
        rw [this]
        rfl
  rw [hall, hU j hj, hr j hj]
  have := cube_mem j hjm
  unfold cubeOK at this
  simpa using this

end CertificateChecks.KernelLC.Co3Id

end
