module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA6Inputs
public import Certificates.Data.Kernel.FootePk
public import CFSG.Certificates.Kernel.FootePkSound
import all Init.Data.Nat.Fold

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A6
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk

@[expose] def q0Lit2016K : List (Equiv.Perm (Fin 10)) :=
  [List.formPerm [0, 9] * List.formPerm [4, 8] * List.formPerm [5, 7],
   List.formPerm [0, 7, 9, 8] * List.formPerm [3, 5, 6, 4],
   List.formPerm [0, 3, 9, 6] * List.formPerm [1, 2] * List.formPerm [4, 7, 5, 8],
   List.formPerm [0, 6] * List.formPerm [1, 2] * List.formPerm [3, 9] * List.formPerm [7, 8],
   List.formPerm [0, 8, 9, 7] * List.formPerm [3, 4, 6, 5],
   List.formPerm [0, 6, 9, 3] * List.formPerm [1, 2] * List.formPerm [4, 8, 5, 7],
   List.formPerm [0, 4, 9, 5] * List.formPerm [3, 7, 6, 8],
   List.formPerm [0, 4, 6, 7, 9, 5, 3, 8],
   List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [4, 8] * List.formPerm [5, 7],
   List.formPerm [0, 5, 9, 4] * List.formPerm [3, 8, 6, 7],
   List.formPerm [0, 8, 6, 4, 9, 7, 3, 5] * List.formPerm [1, 2],
   List.formPerm [0, 6] * List.formPerm [3, 9] * List.formPerm [4, 5],
   List.formPerm [0, 4, 3, 8, 9, 5, 6, 7] * List.formPerm [1, 2],
   List.formPerm [0, 7, 3, 4, 9, 8, 6, 5],
   List.formPerm [0, 4] * List.formPerm [1, 2] * List.formPerm [3, 7] * List.formPerm [5, 9] *
     List.formPerm [6, 8],
   List.formPerm [0, 6, 9, 3] * List.formPerm [4, 7, 5, 8],
   List.formPerm [0, 7] * List.formPerm [1, 2] * List.formPerm [3, 5] * List.formPerm [4, 6] *
     List.formPerm [8, 9],
   List.formPerm [0, 9] * List.formPerm [3, 6] * List.formPerm [4, 5] * List.formPerm [7, 8],
   List.formPerm [3, 6] * List.formPerm [4, 7] * List.formPerm [5, 8],
   List.formPerm [0, 3] * List.formPerm [1, 2] * List.formPerm [4, 5] * List.formPerm [6, 9],
   List.formPerm [0, 8] * List.formPerm [1, 2] * List.formPerm [3, 4] * List.formPerm [5, 6] *
     List.formPerm [7, 9],
   List.formPerm [0, 9] * List.formPerm [1, 2] * List.formPerm [3, 6],
   List.formPerm [0, 9] * List.formPerm [1, 2] * List.formPerm [4, 7] * List.formPerm [5, 8],
   List.formPerm [0, 5, 6, 8, 9, 4, 3, 7],
   List.formPerm [1, 2] * List.formPerm [4, 5] * List.formPerm [7, 8],
   List.formPerm [0, 3] * List.formPerm [6, 9] * List.formPerm [7, 8],
   List.formPerm [0, 7, 6, 5, 9, 8, 3, 4] * List.formPerm [1, 2],
   List.formPerm [0, 5, 3, 7, 9, 4, 6, 8] * List.formPerm [1, 2],
   List.formPerm [0, 8, 3, 5, 9, 7, 6, 4],
   List.formPerm [0, 5] * List.formPerm [1, 2] * List.formPerm [3, 8] * List.formPerm [4, 9] *
     List.formPerm [6, 7],
   List.formPerm [0, 3, 9, 6] * List.formPerm [4, 8, 5, 7],
   1]

@[expose] def xA2016K : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 1] * List.formPerm [2, 9] * List.formPerm [3, 6] * List.formPerm [4, 7]

@[expose] def yA2016K : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 6, 3, 9] * List.formPerm [1, 4, 2, 5]

@[expose] def xB2016K : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 2, 9, 8, 7] * List.formPerm [1, 5, 6, 3, 4]

@[expose] def yB2016K : Equiv.Perm (Fin 10) :=
  List.formPerm [0, 5, 2, 4, 9] * List.formPerm [1, 6, 8, 7, 3]

@[expose] def wit2016K : List (List (Equiv.Perm (Fin 10))) :=
  [[pa, xA2016K, yA2016K], [pa, xB2016K, yB2016K]]

theorem q0V_2016K : searchV 4 ([q1, q2, q3, q4].map codeV) 64 (1 <<< keyV 4 (oneV 10))
    [oneV 10] [oneV 10] = q0Lit2016K.map codeV := by decide +kernel

theorem closed_2016K : closedCheck q0Lit2016K = true := by decide +kernel

theorem nodup_2016K : q0Lit2016K.Nodup := by decide +kernel

theorem length_2016K : q0Lit2016K.length = 2 ^ 5 := by decide +kernel

theorem sift_2016K : (q0Lit2016K.all fun g => siftP QA g 0) = true := by decide +kernel

theorem ab_2016K : (a0 ∈ q0Lit2016K ∧ b0 ∈ q0Lit2016K) ∧
    (siftP QP a0 0 = true ∧ siftP QP b0 0 = true) ∧ dihB a0 b0 = true := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem witSift_2016K : ([pa, xA2016K, yA2016K, xB2016K, yB2016K].all fun c => siftP QP c 0) =
    true := by decide +kernel

theorem witPair_2016K :
    pairWitsV (q0Lit2016K.map codeV) (wit2016K.map (List.map codeV)) = true := by
  decide +kernel

theorem pbWordA_2016K : pb = yA2016K * yA2016K * xA2016K * yA2016K * xA2016K := by decide +kernel

theorem pbWordB_2016K : pb = yB2016K * xB2016K * pa := by decide +kernel

end CertificateChecks.KernelSchreierFam
