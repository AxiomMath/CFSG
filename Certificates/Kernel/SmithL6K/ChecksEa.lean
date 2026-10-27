module

public import Certificates.Data.Kernel.SmithL6KEa
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataW
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem ea_c8_ok : c8K tcl = true := by decide +kernel

theorem ea_w_ok : wK wtP = true := by decide +kernel

theorem ea_f4_ok : f4K tcP idxP tcl = true := by decide +kernel

theorem ea_rig1_ok : rig1K tcP idxP eaG = true := by decide +kernel

theorem ea_rig2_ok : CFSG.Decide.bitsetNodup ((List.range 1953).map (profKey tcP eaG)) = true := by
  decide +kernel

end CertificateChecks.KernelSmithL6K
