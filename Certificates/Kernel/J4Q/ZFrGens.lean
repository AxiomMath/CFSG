module

public import Certificates.Data.Kernel.J4Q.ZFr
public import Certificates.Kernel.J4Q.Mat
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
  CFSG.QuasithinUnique.A5

theorem zcLocWf_true : zcLocWf = true := by
  have hm : (locMats ()).all CFSG.Sporadic.J4.QT2.wfRows = true := by
    rw [Array.all_eq_true]
    intro i hi
    have h := (loc_gens i).1
    rw [Array.getElem?_eq_getElem hi, Option.getD_some] at h
    exact wf_bool h
  have hv : (locInvs ()).all CFSG.Sporadic.J4.QT2.wfRows = true := by
    rw [Array.all_eq_true]
    intro i hi
    have h := (loc_invs i).1
    rw [Array.getElem?_eq_getElem hi, Option.getD_some] at h
    exact wf_bool h
  have hs1 : (locMats ()).size = 3 := by simp [locMats, localWords]
  have hs2 : (locInvs ()).size = 3 := by simp [locInvs, locMats, localWords]
  unfold zcLocWf
  rw [hm, hv, hs1, hs2]
  rfl

theorem zfGens_tabs : ((List.range 3).all fun g =>
    lenOK (zcGenTabs.getD g []) && actT (zcGenTabs.getD g []) 1 == 1) = true := by decide

theorem zfGensOK_true : zfGensOK = true := by
  unfold zfGensOK
  rw [zcLocWf_true, zfGens_tabs]
  rfl

end CertificateChecks.KernelJ4Q

end
