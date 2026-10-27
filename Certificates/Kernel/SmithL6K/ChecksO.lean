module

public import Certificates.Data.Kernel.SmithL6KO
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW
public import Certificates.Kernel.SmithL6K.DataO

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.CollK

theorem sgn_ok : (sgn.all (· < 1953) && sgn.map (fun p => tcl.getD p []) == sgc &&
    sgc.all fun T => apK T (fldW 20 wtP 0) == fldW 20 wtP 0) = true := by decide +kernel

theorem p0_ok : p0K tcP (wmk.getD 0 0) (anm.getD 0 0) = p0 := by decide +kernel

theorem sgu_ok : sgn.map (ucolsK tcP idxP p0) = sgu := by decide +kernel

theorem s2a_ok : s2AK s2m = true := by decide +kernel

theorem s2b_ok : s2BK s2m s2w = true := by decide +kernel

theorem otr_ok : treeK 1395 sgn.length (fun j => j == dRootK wmP (meetK wmP j)) (oEdgeK wtP wmP sgc)
    ort otr = true := by decide +kernel

theorem utr_ok : treeK 512 sgn.length (fun v => v == uRootK s2m (uClsK s2m v)) (uEdgeK s2m sgu)
    urt utr = true := by decide +kernel

theorem ucnt_ok : ((List.range 512).countP (fun v => uClsK s2m v == 1) == 49 &&
    (List.range 512).countP (fun v => uClsK s2m v == 2) == 294 &&
    (List.range 512).countP (fun v => uClsK s2m v == 3) == 168) = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
