module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.C13607Data
public import Certificates.Data.Kernel.SporSch.HNXPtL
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN13607

open CFSG.KC.LL.HNX CFSG.KD.HN13607 CFSG.KD.LgHNX

local notation "R" => CFSG.KD.HNPt.R

theorem w_UW : wordC R uc = U ∧ wordC R wc = W := by decide +kernel

theorem t_UW : trM U = TU ∧ trM W = TW := by decide +kernel

theorem fx_U : ptsFn TX MS CM3 M TU (lget FXE) (lget FXE) 4 = true := by quickRfl

end CertificateChecks.KernelSporSch.HN13607

end
