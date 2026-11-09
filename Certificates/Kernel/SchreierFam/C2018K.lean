module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallL27Inputs
public import Certificates.Data.Kernel.FootePk
public import CFSG.Certificates.Kernel.FootePkSound
import all Init.Data.Nat.Fold

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.L27
  CFSG.GH74.KGroups CFSG.GH74.KGroups.L27 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk

@[expose] def q0Lit2018K : List (Equiv.Perm (Fin 8)) :=
  [List.formPerm [0, 3] * List.formPerm [1, 4] * List.formPerm [2, 7] * List.formPerm [5, 6],
   List.formPerm [0, 3, 1, 5, 7, 2, 6, 4],
   List.formPerm [0, 7] * List.formPerm [2, 4] * List.formPerm [3, 5],
   List.formPerm [0, 7] * List.formPerm [1, 6] * List.formPerm [2, 3] * List.formPerm [4, 5],
   List.formPerm [0, 6, 7, 1] * List.formPerm [2, 5, 3, 4],
   List.formPerm [0, 6] * List.formPerm [1, 7] * List.formPerm [2, 3],
   List.formPerm [0, 5, 6, 3, 7, 4, 1, 2],
   List.formPerm [0, 5] * List.formPerm [1, 3] * List.formPerm [2, 6] * List.formPerm [4, 7],
   List.formPerm [0, 4] * List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [5, 7],
   List.formPerm [0, 4, 6, 2, 7, 5, 1, 3],
   List.formPerm [0, 1] * List.formPerm [4, 5] * List.formPerm [6, 7],
   List.formPerm [0, 1, 7, 6] * List.formPerm [2, 4, 3, 5],
   List.formPerm [1, 6] * List.formPerm [2, 5] * List.formPerm [3, 4],
   List.formPerm [0, 2] * List.formPerm [1, 5] * List.formPerm [3, 7] * List.formPerm [4, 6],
   List.formPerm [0, 2, 1, 4, 7, 3, 6, 5],
   1]

@[expose] def xA2018K : Equiv.Perm (Fin 8) := List.formPerm [1, 4, 2] * List.formPerm [3, 5, 6]

@[expose] def yA2018K : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 3] * List.formPerm [1, 6] * List.formPerm [2, 4] * List.formPerm [5, 7]

@[expose] def xB2018K : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 1, 3, 4] * List.formPerm [2, 6, 7, 5]

@[expose] def yB2018K : Equiv.Perm (Fin 8) :=
  List.formPerm [0, 6, 4, 3] * List.formPerm [1, 7, 2, 5]

@[expose] def wit2018K : List (List (Equiv.Perm (Fin 8))) :=
  [[pa, xA2018K, yA2018K], [pa, xB2018K, yB2018K]]

theorem q0V_2018K : searchV 3 ([q1, q2].map codeV) 64 (1 <<< keyV 3 (oneV 8)) [oneV 8]
    [oneV 8] = q0Lit2018K.map codeV := by decide +kernel

theorem closed_2018K : closedCheck q0Lit2018K = true := by decide +kernel

theorem nodup_2018K : q0Lit2018K.Nodup := by decide +kernel

theorem length_2018K : q0Lit2018K.length = 2 ^ 4 := by decide +kernel

theorem sift_2018K : (q0Lit2018K.all fun g => siftP QA g 0) = true := by decide +kernel

theorem ab_2018K : (a0 ∈ q0Lit2018K ∧ b0 ∈ q0Lit2018K) ∧
    (siftP QP a0 0 = true ∧ siftP QP b0 0 = true) ∧ dihB a0 b0 = true := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem witSift_2018K : ([pa, xA2018K, yA2018K, xB2018K, yB2018K].all fun c => siftP QP c 0) =
    true := by decide +kernel

theorem witPair_2018K :
    pairWitsV (q0Lit2018K.map codeV) (wit2018K.map (List.map codeV)) = true := by
  decide +kernel

theorem pbWordA_2018K : pb = yA2018K * xA2018K * yA2018K := by decide +kernel

theorem pbWordB_2018K : pb = yB2018K * xB2018K := by decide +kernel

end CertificateChecks.KernelSchreierFam
