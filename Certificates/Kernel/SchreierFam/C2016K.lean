module

public import CFSG.LocalAnalysis.ComponentClassification.FooteSmallA6Inputs
public import Certificates.Data.Kernel.FootePk
import all Init.Data.Nat.Fold

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam

open CFSG.ComponentClassification.FooteSmall CFSG.ComponentClassification.FooteSmall.A6
  CFSG.GH74.KGroups CFSG.GH74.KGroups.A6 CFSG.Certificates.Kernel.PkEnum
  CFSG.Certificates.Kernel.FootePk

theorem closed_2016K : closedCheck Q0list = true := by decide +kernel

theorem nodup_2016K : Q0list.Nodup := by decide +kernel

theorem length_2016K : Q0list.length = 2 ^ 5 := by decide +kernel

theorem sift_2016K : (Q0list.all fun g => siftP QA g 0) = true := by decide +kernel

theorem ab_2016K : (a0 ∈ Q0list ∧ b0 ∈ Q0list) ∧ (siftP QP a0 0 = true ∧ siftP QP b0 0 = true) ∧
    dihB a0 b0 = true := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> decide +kernel

theorem pair_2016K :
    pairCheckV 3 4 (Q0list.map codeV) (enumV (strongV QP) QP.base) ([pa, pb].map codeV) = true := by
  decide +kernel

end CertificateChecks.KernelSchreierFam
