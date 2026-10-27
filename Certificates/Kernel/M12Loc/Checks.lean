module

public import Certificates.Data.Kernel.M12Loc
public import Certificates.Kernel.M12Loc.Data

public section

namespace CertificateChecks.KernelM12Loc

open CFSG.KC.M12Loc CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12

theorem TT_eq : D.TT = trT := by decide +kernel

theorem nz_list : listOK (predP zT) D.TT idxNP D.TNP = true := by decide +kernel

theorem nz_swap : D.TNP.any (fun t => tconj t zT == tpow zT 2) = true := by decide +kernel

theorem count_NP : countOK (predN [xT, yT] P0T) D.TNP 108 = true := by decide +kernel

theorem count_CE : countOK (predC [zT, xT]) D.TNP 9 = true := by decide +kernel

theorem count_CF : countOK (predC [zT, yT]) D.TNP 9 = true := by decide +kernel

theorem count_NA : countOK (predN [zT, aT] AT) D.TNP 54 = true := by decide +kernel

theorem count_CA : countOK (predC [zT, aT]) D.TNP 9 = true := by decide +kernel

theorem np_ok : npOK D.TNP = true := by decide +kernel

theorem center_ok : centerOK = true := by decide +kernel

theorem afix_ok : aFixOK = true := by decide +kernel

theorem na_list : listOK (predP aT) D.TT idxNa D.TNa = true := by decide +kernel

theorem orb_ok : orbOK D.W = true := by decide +kernel

theorem psi_rows_0 : psiRows (D.TNa.take 24) D.TNa = true := by decide +kernel

theorem psi_rows_1 : psiRows ((D.TNa.drop 24).take 24) D.TNa = true := by decide +kernel

theorem psi_rows_2 : psiRows (D.TNa.drop 48) D.TNa = true := by decide +kernel

theorem psi_val : psiValOK D.TNa = true := by decide +kernel

theorem nz_list_neg : listOK (predP zT) D.TT idxNP D.TNP.reverse = false := by decide +kernel

theorem count_NP_neg : countOK (predN [xT, yT] P0T) D.TNP 107 = false := by decide +kernel

theorem orb_neg : orbOK D.W.reverse = false := by decide +kernel

theorem psi_neg : psiRows [tid] [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 10]] = false := by
  decide +kernel

theorem psi_val_neg : psiValOK [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] = false := by decide +kernel

theorem T3_eq : CFSG.RankThree.PartTwo.Toolkit.perms3.map CFSG.RankThree.PartTwo.Toolkit.ptab = T3L := by
  decide +kernel

theorem T4e_eq : (CFSG.RankThree.PartTwo.Toolkit.perms4.filter fun σ => decide (Equiv.Perm.sign σ = 1)).map
    CFSG.RankThree.PartTwo.Toolkit.ptab = T4eL := by
  decide +kernel

end CertificateChecks.KernelM12Loc

end
