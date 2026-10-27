module

public import Certificates.Data.Kernel.L5.Sh2Chk
public import Certificates.Data.Kernel.L5.GrpOf
public import CFSG.Certificates.Kernel.Common.DecideFV

public section

namespace CFSG.KD.L5

open CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.Fus CFSG.KD

theorem sh2MulChk_true : sh2MulChk = true := by decide +kernel

end CFSG.KD.L5

end
