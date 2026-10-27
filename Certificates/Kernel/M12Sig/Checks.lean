module

public import Certificates.Data.Kernel.M12Sig
public import Certificates.Kernel.M12Cent.Data

public section

namespace CertificateChecks.KernelM12Sig

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
  CFSG.KC.M12Cent CFSG.KC.M12Sig

theorem normal_ok : chkNormal = true := by decide +kernel

theorem vstruct_ok : chkVStruct = true := by decide +kernel

theorem gamma_ok : chkGamma = true := by decide +kernel

theorem centL_ok : centL = true := by decide +kernel

theorem outer_ok : outerB g1W zbT abT CertificateChecks.KernelM12Cent.D.C = true := by
  decide +kernel

theorem vv_ok : vvB VT = true := by decide +kernel

theorem inv_ok : invB invW = true := by decide +kernel

theorem twoC_ok : twoC VT = true := by decide +kernel

theorem xconj_ok : xconjB xT = true := by decide +kernel

theorem outer_neg : outerB g1W zbT (tconj (tinv (wordN g1W)) aT) [[]] = false := by
  decide +kernel

theorem vv_neg : vvB (fun _ => VT 0) = false := by decide +kernel

theorem inv_neg : invB [] = false := by decide +kernel

theorem twoC_neg : twoC (fun _ => []) = false := by decide +kernel

theorem xconj_neg : xconjB yT = false := by decide +kernel

end CertificateChecks.KernelM12Sig

end
