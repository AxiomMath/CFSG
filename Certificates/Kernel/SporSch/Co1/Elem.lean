module

public import Certificates.Kernel.SporSch.Co1.ElemDag
public meta import Certificates.Kernel.SporSch.GenPerms
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.GenPerms

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Elem

meta def QA : Array (Array Nat) :=
  #[CFSG.Sporadic.Co1Schreier.Native.qMat,
    CFSG.Sporadic.Co1Schreier.Native.inv CFSG.Sporadic.Co1Schreier.Native.qMat]

end CertificateChecks.KernelSporSch.Co1Elem

#kss_perms CertificateChecks.KernelSporSch.Co1Elem.QP 24 CertificateChecks.KernelSporSch.Co1Elem.QA

namespace CertificateChecks.KernelSporSch.Co1Elem

open CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native

theorem kElem : elemK AF = true := by quickRfl
theorem kEig : eigenK AF (E.M 2) (QP 0) (QP 1) Data.f4vecs Data.eigenchars = true := by quickRfl

theorem elem : elemCheck = true := by
  unfold elemCheck
  rw [dag_eq, aRows_eq]
  simpa using elemK_sound kElem

theorem eigen : eigenCheck = true := by
  have h : eigenCheck = eigenP aRows zR Data.f4vecs Data.eigenchars := rfl
  rw [h, aRows_eq, zR_eq]
  exact eigenK_sound kEig

end CertificateChecks.KernelSporSch.Co1Elem

end
