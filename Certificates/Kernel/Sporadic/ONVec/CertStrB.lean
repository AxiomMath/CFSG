module

public import Certificates.Kernel.Sporadic.ONVec.CertStrA

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.ON (TT UU)

theorem strong_inv : allBelowN 7 (fun j => pisInv 245520 (TTA[j]!) ((pinvs 245520 TTA)[j]!)) = true := by
  refine allBelowN_of fun j hj => ?_
  unfold pisInv
  refine allBelowN_of fun x hx => ?_
  have hpf := ON.perm_facts' x hx j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [ofFn_get2 hj hx, (pinvs_TTA j hj) _ hpf.1]
  exact ⟨hpf.1, hpf.2.2⟩

end CertificateChecks.KernelSpor.ONVec

end
