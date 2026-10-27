module

public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import Certificates.Kernel.Th.Dce
public import CFSG.Certificates.Kernel.Th.S.Data.Ot_Sel
public import CFSG.Certificates.Kernel.Th.Checks2.Ot_X
public import CFSG.Certificates.Kernel.Th.Checks2.Ot_B

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelTh

open CFSG.KC.Th.Gen

#th_assemble dceStruct DceStructData dceStructChkGen

theorem dceStruct_pins : dceStructPins dceStructData = true := by decide +kernel

theorem dceStruct_chk : dceStructChk dceStructData = true := andB_true dceStruct_ok dceStruct_pins

end CertificateChecks.KernelTh

end
