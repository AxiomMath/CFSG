module

public import Certificates.Kernel.SporSch.J4S.NCharChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J4NChar

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch

theorem neg_forest_gen : Bool.not (forestK J4IC.T [(3, 0, 0), (199, 0, 1)]) = true := by quickRfl

theorem neg_forest_parent : Bool.not (forestK J4IC.T [(3, 0, 0), (199, 1, 0)]) = true := by quickRfl

theorem neg_forest_empty : Bool.not (forestK J4IC.T []) = true := by quickRfl

theorem neg_wit_none : Bool.not (witK J4E.T uClasses[0]! none) = true := by quickRfl

theorem neg_wit_zero : Bool.not (witK J4E.T [(118, 0, 0)] (some (0, 0, 0))) = true := by quickRfl

theorem neg_wit_range : Bool.not (witK J4E.T [(3, 0, 0), (199, 0, 0)] (some (0, 2, 2))) = true := by
  quickRfl

theorem neg_cover : Bool.not (coverK J4E.T []) = true := by quickRfl

theorem neg_fix2 : Bool.not (Nat.beq (fix2CntK (J4E.T 118) (J4E.T 448)) 31) = true := by quickRfl

theorem neg_quad : Bool.not (allN 2048 (fun v => quadK (J4E.T 3) (J4E.T 199) v)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.J4NChar

end
