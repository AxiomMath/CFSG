module

public import Certificates.Data.Kernel.SmithL6KU
public import Certificates.Kernel.SmithL6K.Data
public import Certificates.Kernel.SmithL6K.DataO

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K

theorem ua_gens_ok : ugens.toList.all (fun g => decide (g < 1953) && p0.contains g) = true := by
  decide +kernel

theorem ua_uco_ok : ((List.range 49).all fun k => decide (0 < uco[k]!) && decide (uco[k]! < 512) &&
    (List.range k).all fun l => uco[l]! != uco[k]!) = true := by
  decide +kernel

theorem ua_slices_ok : ∀ k < 49, (((uaRC tvc p0).drop (7 * (k / 7))).take 7).contains
    (uco[k]!, tvc.getD (p0.getD k 0) 0) = true := by
  decide +kernel

theorem ua_fix_ok : uaFixC tvc p0 = true := by decide +kernel

theorem ua_move_ok : uaMoveC (ugC tvc) tvc = true := by decide +kernel

theorem ua_comm_ok : uaCommC tvc p0 = true := by decide +kernel

theorem ua_planes_ok : uaPlanesK (p0.map (tcl.getD · [])) wtd = true := by decide +kernel

end CertificateChecks.KernelSmithL6K
