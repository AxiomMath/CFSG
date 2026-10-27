module

public import Certificates.Kernel.SporSch.HN.C13609Data
public import Certificates.Data.Kernel.SporSch.ConjKey
public import Certificates.Data.Kernel.SporSch.HNXPrim
public import CFSG.Certificates.Kernel.Local.HN.Lib
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HN13609

open CFSG.KC.ConjKey CFSG.KS.SporSch CFSG.KD.HN13609

local notation "mm" => CFSG.KC.LL.HN.mm
local notation "G3" => CFSG.KD.HNPt2109.G3F

theorem valid_CI : CFSG.KC.Enum.allN 7 (fun j => validHN (CIF j)) = true := by quickRfl

theorem inv_CI :
    CFSG.KC.Enum.allN 7 (fun j => eqK (mm (G3 j) (CIF j)) CFSG.KD.OrdHN.ONE) = true := by
  quickRfl

theorem y_eq : eqK (mm (mm (G3 6) (G3 0)) (G3 0)) Y = true := by quickRfl

theorem y_pow : eqK (mm (mm (mm (mm Y Y) Y) Y) Y) CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem keys : conjKeysOK vmHN G3 CIF 8 Y 1 W 972 = true := by quickRfl

end CertificateChecks.KernelSporSch.HN13609

end
