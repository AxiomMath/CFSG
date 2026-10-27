module

public import Certificates.Kernel.F4Gamma.Data
public import Certificates.Data.Kernel.F4Gamma

public section

namespace CFSG.KD.F4Gamma

open CFSG.KC.F4Gamma CFSG.KC.F4Rank CFSG.KC.F4Syl3

theorem basis_ok : basisChk bb = true := by decide +kernel

theorem flag_ok : allN 3 (fun k => flagChk bb (gs.getD k 0) (cs.getD k 0)) = true := by
  decide +kernel

theorem lam_ok : coordChk lam bb 48 = true := by decide +kernel

theorem mu_ok : coordChk mu bb 49 = true := by decide +kernel

theorem chi_ok : allN 3 (fun k => dotR lam (vapp (gs.getD k 0) (colR bb 49)) ==
    dotR mu (vapp (gs.getD k 0) (colR bb 50))) = true := by
  decide +kernel

theorem chi_one : dotR lam (vapp (gs.getD 0 0) (colR bb 49)) = 1 := by decide +kernel

theorem orb1_ok : orbChk gs w1 pp1 rr1 64 = true := by decide +kernel

theorem stab_ok : allN 3 (fun j => stabRow gs hs hw w1 j) = true := by decide +kernel

theorem hs_length : hs.length = 3 := by decide +kernel

theorem gs_length : gs.length = 3 := by decide +kernel

theorem orb2_ok : orbChk hs w2 pp2 rr2 64 = true := by decide +kernel

end CFSG.KD.F4Gamma

end
