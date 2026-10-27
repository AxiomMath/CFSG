module

public import Certificates.Data.Kernel.SmithL6KW
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataG
public import Certificates.Kernel.SmithL6K.DataW
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem wtd_nodup : CFSG.Decide.bitsetNodup wtd = true := by decide +kernel

theorem pin_wtP : pinF (fldW 20 wtP) 0 wtd = true := by decide +kernel

theorem pin_wmP : pinF (fldW 64 wmP) 0 wmk = true := by decide +kernel

theorem gns_len : gns.length = 6 := by decide +kernel

theorem close_ok0 : closeRowK (tcl.getD (gns.getD 0 0) []) (fldW 12 tcP (gns.getD 0 0))
    (gpP.getD 0 0) wtP wmP = true := by decide +kernel

theorem close_ok1 : closeRowK (tcl.getD (gns.getD 1 0) []) (fldW 12 tcP (gns.getD 1 0))
    (gpP.getD 1 0) wtP wmP = true := by decide +kernel

theorem close_ok2 : closeRowK (tcl.getD (gns.getD 2 0) []) (fldW 12 tcP (gns.getD 2 0))
    (gpP.getD 2 0) wtP wmP = true := by decide +kernel

theorem close_ok3 : closeRowK (tcl.getD (gns.getD 3 0) []) (fldW 12 tcP (gns.getD 3 0))
    (gpP.getD 3 0) wtP wmP = true := by decide +kernel

theorem close_ok4 : closeRowK (tcl.getD (gns.getD 4 0) []) (fldW 12 tcP (gns.getD 4 0))
    (gpP.getD 4 0) wtP wmP = true := by decide +kernel

theorem close_ok5 : closeRowK (tcl.getD (gns.getD 5 0) []) (fldW 12 tcP (gns.getD 5 0))
    (gpP.getD 5 0) wtP wmP = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
