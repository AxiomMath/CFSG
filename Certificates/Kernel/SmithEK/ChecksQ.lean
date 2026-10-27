module

public import Certificates.Data.Kernel.SmithEKQ
public import Certificates.Kernel.SmithEK.QData
public import Certificates.Kernel.SmithEK.WData
public import Certificates.Kernel.SmithEK.MData
public import Certificates.Kernel.SmithEK.Cols

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21267qa_0 : qaChkE wd.W wd.M pb.P cs.L qz.QG qz.QU = true := by
  decide +kernel

theorem c21267cv_0 : cvChkE wd.W pb.P cs.L qz.CG qz.CU = true := by
  decide +kernel

end CertificateChecks.KernelSmithEK
