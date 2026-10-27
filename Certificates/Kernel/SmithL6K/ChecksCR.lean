module

public import Certificates.Data.Kernel.SmithL6KC
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW
public import Certificates.Kernel.SmithL6K.DataC

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6.K

theorem cx_pins : (cxU == ugC tvc && cxL == [tvc.getD 0 0, tvc.getD 224 0] &&
    anm.length == 1395 && anm.zipIdx.all (fun p => fldW 64 cxAn p.2 == p.1)) = true := by
  decide +kernel

theorem cx_repsM : (cxRM == repsC.map fun r => candM cxU cxL r.1 r.2) = true := by
  decide +kernel

theorem cx_rep0 : repOK cxU cxL wtP wmP cxAn 0 (cxR.getD 0 []) = true := by decide +kernel

theorem cx_rep1 : repOK cxU cxL wtP wmP cxAn 1 (cxR.getD 1 []) = true := by decide +kernel

theorem cx_rep2 : repOK cxU cxL wtP wmP cxAn 2 (cxR.getD 2 []) = true := by decide +kernel

theorem cx_rep3 : repOK cxU cxL wtP wmP cxAn 3 (cxR.getD 3 []) = true := by decide +kernel

theorem cx_rep4 : repOK cxU cxL wtP wmP cxAn 4 (cxR.getD 4 []) = true := by decide +kernel

theorem cx_fp : fpOK (candC cxU cxL 4 0) tvc tcP wtP wmP cxAn cxBs cxPl cxPm cxUm cxFx cxFt
    cxB6 = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
