module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.OddCore.LinesICmd
public import CFSG.Certificates.Kernel.Spor.DecLinesISound
public import CFSG.Sporadic.HNOddCore.DCheckInputs
meta import CFSG.Sporadic.HNOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.HNT.PAR CFSG.Sporadic.HNOddCore.InvData.parText
#ks_linesI CertificateChecks.KernelSpor.HNT.PAR CFSG.Sporadic.HNOddCore.InvData.parRecs
#ks_chars CertificateChecks.KernelSpor.HNT.CPAR CFSG.Sporadic.HNOddCore.InvData.cparText
#ks_linesI CertificateChecks.KernelSpor.HNT.CPAR CFSG.Sporadic.HNOddCore.InvData.cparRecs
#ks_chars CertificateChecks.KernelSpor.HNT.VPAR CFSG.Sporadic.HNOddCore.InvData.vparText
#ks_linesI CertificateChecks.KernelSpor.HNT.VPAR CFSG.Sporadic.HNOddCore.InvData.vparRecs

namespace CertificateChecks.KernelSpor.HND

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.InvData CFSG.Sporadic.HNOddCore.Native
open CFSG.KS.DecLines

theorem par_eq : parRecs = HNT.PAR.E.toArray := by
  unfold parRecs; rw [HNT.PAR.eq]; exact intLinesOf_ofList HNT.PAR.ok
theorem cpar_eq : cparRecs = HNT.CPAR.E.toArray := by
  unfold cparRecs; rw [HNT.CPAR.eq]; exact intLinesOf_ofList HNT.CPAR.ok
theorem vpar_eq : vparRecs = HNT.VPAR.E.toArray := by
  unfold vparRecs; rw [HNT.VPAR.eq]; exact intLinesOf_ofList HNT.VPAR.ok

theorem shapeI_of {L : List (List Int)} {k m : Nat}
    (h : (L.length == k && L.all (fun a => a.length == m)) = true) :
    (L.toArray.size == k && allLength L.toArray m) = true := by
  simpa [allLength, List.all_toArray] using h

theorem par_shape : (parRecs.size == 16384 && allLength parRecs 2) = true := by
  rw [par_eq]; exact shapeI_of (by decide +kernel)
theorem cpar_shape : (cparRecs.size == 14400 && allLength cparRecs 2) = true := by
  rw [cpar_eq]; exact shapeI_of (by decide +kernel)
theorem vpar_shape : (vparRecs.size == 4608 && allLength vparRecs 2) = true := by
  rw [vpar_eq]; exact shapeI_of (by decide +kernel)

end CertificateChecks.KernelSpor.HND

end
