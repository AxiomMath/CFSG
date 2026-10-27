module

public import Certificates.Kernel.HSStd.U43Z4Cv
public import Certificates.Kernel.HSStd.U43Z4S0
public import Certificates.Kernel.HSStd.U43Z4S1
public import Certificates.Kernel.HSStd.U43Z4S2
public import Certificates.Kernel.HSStd.U43Z4S3
public import Certificates.Kernel.HSStd.U43Z4S4
public import CFSG.Certificates.Kernel.Common.ListSlices
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case CertificateChecks.KernelHSStd
  CFSG.KS.ListSlices

#kc_forall_tree ksCand_all (fun s => CertificateChecks.KernelHSStd.U43Z4.ksCand s = true) 8
  CertificateChecks.KernelHSStd.U43Z4.ksCand
#kc_forall_tree ksK_all (fun g => CertificateChecks.KernelHSStd.U43Z4.ksK g = true) 4
  CertificateChecks.KernelHSStd.U43Z4.ksK
#kc_forall_tree ksC_all (fun g => CertificateChecks.KernelHSStd.U43Z4.ksC g = true) 4
  CertificateChecks.KernelHSStd.U43Z4.ksC

theorem z4_cand : (List.range Z4Y.cnt).filter (fun i => candP 820 10 (Z4P 0) (Z4P 1) (Z4Y.T i)) =
    z4IC.flatten := by
  have hN : Z4Y.cnt = 243 * 8 := rfl
  rw [hN, List.range_eq_range', filter_slices _ 243 z4IC 8 fun s hs => ksCand_all s hs]
  decide

theorem z4_k : ∀ e ∈ z4KG.flatten,
    (List.range Z4Y.cnt).filter (fun j => kP 820 10 (Z4P 0) (Z4Y.T e.1) (Z4Y.T j)) = e.2 := by
  have h := all_flatten _ z4KG fun g hg => ksK_all g hg
  rw [List.all_eq_true] at h
  exact fun e he => beq_iff_eq.mp (h e he)

theorem z4_sols : solsP 820 10 (Z4P 0) (Z4P 1) Z4Y.cnt Z4Y.T = z4CG.flatten := by
  have hfst : z4KG.flatten.map Prod.fst = z4IC.flatten := by decide
  unfold solsP
  rw [z4_cand, ← hfst,
    flatMap_pairs_eq (fun i => (List.range Z4Y.cnt).filter fun j =>
      kP 820 10 (Z4P 0) (Z4Y.T i) (Z4Y.T j)) _ z4_k]
  decide

theorem kSol : solK 820 10 (Z4P 0) (Z4P 1) Z4Y.cnt Z4Y.T 12 = true := by
  unfold solK
  rw [z4_sols, Bool.and_eq_true]
  exact ⟨by decide, all_flatten _ z4CG fun g hg => ksC_all g hg⟩

end CertificateChecks.KernelHSStd.U43Z4

end
