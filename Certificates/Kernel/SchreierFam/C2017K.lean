module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA7Inputs
public import Certificates.Data.Kernel.FootePk
public import CFSG.Certificates.Kernel.FootePkSound
import all Init.Data.Nat.Fold

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A7
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A7 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk

@[expose] def q0Lit2017K : List (Equiv.Perm (Fin 7)) :=
  [List.formPerm [0, 1],
   List.formPerm [0, 1] * List.formPerm [2, 4, 5, 3],
   List.formPerm [0, 1] * List.formPerm [3, 4],
   List.formPerm [2, 4, 5, 3],
   List.formPerm [3, 4],
   List.formPerm [2, 5],
   List.formPerm [2, 4] * List.formPerm [3, 5],
   List.formPerm [0, 1] * List.formPerm [2, 3] * List.formPerm [4, 5],
   List.formPerm [2, 3] * List.formPerm [4, 5],
   List.formPerm [2, 5] * List.formPerm [3, 4],
   List.formPerm [0, 1] * List.formPerm [2, 4] * List.formPerm [3, 5],
   List.formPerm [0, 1] * List.formPerm [2, 5] * List.formPerm [3, 4],
   List.formPerm [2, 3, 5, 4],
   List.formPerm [0, 1] * List.formPerm [2, 5],
   List.formPerm [0, 1] * List.formPerm [2, 3, 5, 4],
   1]

@[expose] def wit2017K : List (Equiv.Perm (Fin 7)) :=
  [pa, List.formPerm [3, 6, 4], List.formPerm [2, 5, 6],
    List.formPerm [0, 1, 6] * List.formPerm [2, 3] * List.formPerm [4, 5]]

theorem q0V_2017K : searchV 6 ([q1, q2, q3].map codeV) 64 (1 <<< keyV 6 (oneV 7)) [oneV 7]
    [oneV 7] = q0Lit2017K.map codeV := by decide +kernel

theorem closed_2017K : closedCheck q0Lit2017K = true := by decide +kernel

theorem nodup_2017K : q0Lit2017K.Nodup := by decide +kernel

theorem length_2017K : q0Lit2017K.length = 2 ^ 4 := by decide +kernel

theorem sift_2017K : (q0Lit2017K.all fun g => siftP QA g 0) = true := by decide +kernel

theorem ab_2017K : (a0 ∈ q0Lit2017K ∧ b0 ∈ q0Lit2017K) ∧
    (siftP QP a0 0 = true ∧ siftP QP b0 0 = true) ∧ dihB a0 b0 = true := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem witSift_2017K : (wit2017K.all fun c => siftP QP c 0) = true := by decide +kernel

theorem witPair_2017K : pairWitV (q0Lit2017K.map codeV) (wit2017K.map codeV) = true := by
  decide +kernel

theorem pbWord_2017K : pb = List.formPerm [3, 6, 4] * List.formPerm [2, 5, 6] *
    (List.formPerm [0, 1, 6] * List.formPerm [2, 3] * List.formPerm [4, 5]) *
    List.formPerm [2, 5, 6] := by decide +kernel

end CertificateChecks.KernelSchreierFam
