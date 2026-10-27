module

public import Certificates.Kernel.SporSch.HN.C13608Data
public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.HNChain.FormK
public import Certificates.Data.Kernel.SporSch.HNXPt
public import Certificates.Data.Kernel.SporSch.HNXPrim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN13608

open CFSG.KC.LL.HNX CFSG.KD.HN13608

local notation "R" => CFSG.KD.HNPt.R
local notation "mm" => CFSG.KC.LL.HN.mm

@[expose] noncomputable def gL13608 : Nat :=
  mm (mm (mm (mm (mm (mm (mm (mm (mm (mm (mm (R 34) (R 35)) (R 35)) (R 34)) (R 35)) (R 34)) (R 35))
    (R 34)) (R 35)) (R 34)) (R 35)) (R 34)

@[expose] def gic13608 : List Nat :=
  [34, 35, 35, 34, 35, 35, 34, 35, 35, 34, 35, 35, 34, 35, 35, 35, 35, 34]

theorem inv_ok : mm gL13608 (wordC R gic13608) = CFSG.KD.OrdHN.ONE := by
  decide +kernel

theorem u_shape : U = mm (R 34) (mm (mm (wordC R gic13608) (R 35)) gL13608) := by
  decide +kernel

theorem words_ok : wordC R uc = U ∧ wordC R ec = E ∧ trM (CFSG.KC.LL.HN.subI E) = GE := by
  decide +kernel

theorem form_ok : CFSG.KS.SporSch.validHN FM = true ∧
    lanesEq FM (CertificateChecks.KernelHNChain.Form.sf 2) = true := by
  decide +kernel

theorem gq_ok :
    GQ = mm FM (CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L CFSG.KD.OrdHN.H 5 9 (U + mm U U)) := by
  decide +kernel

end CertificateChecks.KernelSporSch.HN13608

end
