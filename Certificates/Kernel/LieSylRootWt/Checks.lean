module

public import Certificates.Data.Kernel.LieSylRootWtK
public import Certificates.Kernel.LieSylRootWt.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLieSylRootWt

open Certificates.Data.LieSylRootWt Certificates.Data.LieSylRootWtK CFSG.KD.LieSylRootWt

theorem ch617001D4 : searchK RP_D4 LP_D4 MK_D4 24 4 0 [] = true := by quickRfl

theorem ch617001F4 : searchK RP_F4 LP_F4 MK_F4 24 4 0 [] = true := by quickRfl

theorem ch617001tD4 : (Ty.D4.roots.map pvI == RP_D4) = true := by quickRfl

theorem ch617001lD4 : ((levels4 Ty.D4.roots).map (List.map pvI) == LP_D4) = true := by quickRfl

theorem ch617001mD4 : Nat.beq MK_D4 (maskOf (Ty.D4.roots.map kvI)) = true := by quickRfl

theorem ch617001tF4 : (Ty.F4.roots.map pvI == RP_F4) = true := by quickRfl

theorem ch617001lF4 : ((levels4 Ty.F4.roots).map (List.map pvI) == LP_F4) = true := by quickRfl

theorem ch617001mF4 : Nat.beq MK_F4 (maskOf (Ty.F4.roots.map kvI)) = true := by quickRfl

theorem ch617001G2 : rootWeightStabCheck .G2 11 6 = true := by decide +kernel

end CertificateChecks.KernelLieSylRootWt

end
