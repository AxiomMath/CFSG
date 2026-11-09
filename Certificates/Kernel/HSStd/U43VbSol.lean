module

public import Certificates.Kernel.HSStd.U43VbS0
public import Certificates.Kernel.HSStd.U43VbS1
public import Certificates.Kernel.HSStd.U43VbS2
public import Certificates.Kernel.HSStd.U43VbS3
public import Certificates.Kernel.HSStd.U43VbS4
public import CFSG.Certificates.Kernel.Common.ListSlices
public import CFSG.Certificates.Kernel.Common.ForallTree
meta import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case CertificateChecks.KernelHSStd
  CFSG.KS.ListSlices

#kc_forall_tree ksCand_all (fun s => CertificateChecks.KernelHSStd.U43Vb.ksCand s = true) 8
  CertificateChecks.KernelHSStd.U43Vb.ksCand
#kc_forall_tree ksK_all (fun g => CertificateChecks.KernelHSStd.U43Vb.ksK g = true) 4
  CertificateChecks.KernelHSStd.U43Vb.ksK
#kc_forall_tree ksC_all (fun g => CertificateChecks.KernelHSStd.U43Vb.ksC g = true) 12
  CertificateChecks.KernelHSStd.U43Vb.ksC

theorem vb_cand : (List.range VbY.cnt).filter (fun i => candP 820 10 (VbP 0) (VbP 1) (VbY.T i)) =
    vbIC.flatten := by
  have hc : ∀ t y c, candP 820 10 t y c = candQ 820 10 t y c := fun t y c =>
    (candQ_eq (by norm_num) (by norm_num) t y c).symm
  simp only [hc]
  have hN : VbY.cnt = 243 * 8 := rfl
  rw [hN, List.range_eq_range', filter_slices _ 243 vbIC 8 fun s hs => ksCand_all s hs]
  decide

theorem vb_k : ∀ e ∈ vbKG.flatten,
    (List.range VbY.cnt).filter (fun j => kP 820 10 (VbP 0) (VbY.T e.1) (VbY.T j)) = e.2 := by
  have hk : ∀ t c k, kQ 820 10 t c k = kP 820 10 t c k := kQ_eq (by norm_num) (by norm_num)
  have h := all_flatten (fun e : Nat × List Nat =>
    ((List.range VbY.cnt).filter fun j => kQ 820 10 (VbP 0) (VbY.T e.1) (VbY.T j)) == e.2)
    vbKG fun g hg => ksK_all g hg
  rw [List.all_eq_true] at h
  intro e he
  have h' := beq_iff_eq.mp (h e he)
  simp only [hk] at h'
  exact h'

theorem vb_sols : solsP 820 10 (VbP 0) (VbP 1) VbY.cnt VbY.T = vbCG.flatten := by
  have hfst : vbKG.flatten.map Prod.fst = vbIC.flatten := by decide
  unfold solsP
  rw [vb_cand, ← hfst,
    flatMap_pairs_eq (fun i => (List.range VbY.cnt).filter fun j =>
      kP 820 10 (VbP 0) (VbY.T i) (VbY.T j)) _ vb_k]
  decide

theorem kSol : solK 820 10 (VbP 0) (VbP 1) VbY.cnt VbY.T 12 = true := by
  unfold solK
  rw [vb_sols, Bool.and_eq_true]
  have h := all_flatten (fun p : Nat × Nat =>
    cent5Q 820 10 (VbP 0) VbY.cnt VbY.T (VbY.T p.1) (VbY.T p.2) == 3) vbCG fun g hg => ksC_all g hg
  simp only [cent5Q_eq (by norm_num : 820 < 2 ^ 32) (by norm_num : 0 < 10)] at h
  exact ⟨by decide, h⟩

end CertificateChecks.KernelHSStd.U43Vb

end
