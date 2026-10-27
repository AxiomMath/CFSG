module

public import Certificates.Data.Kernel.SmithL6KOp
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem op_ord4_ok : ord4K tcP = true := by decide +kernel

theorem op_std_ok : stdK tcP = true := by decide +kernel

theorem op_f3_ok : f3K tcP idxP wtP tcl = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
