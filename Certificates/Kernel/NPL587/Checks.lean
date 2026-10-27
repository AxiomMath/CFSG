module

public import Certificates.Data.Kernel.NPL587K
public import Certificates.Kernel.NPL587.Data

set_option maxRecDepth 100000

public section

namespace CFSG.KD.NPL587.Chk

open CFSG.Quasithin.H13.NPLK CFSG.KD.NPL587

theorem s0_ok : s0OK gens s0 s0w = true := by decide +kernel

theorem reps_ok : reps.all (repOK gens s0) = true := by decide +kernel

theorem repc_ok : (repc == reps.map Prod.fst) = true := by decide +kernel

theorem ql_ok : ql.all (qOK repc) = true := by decide +kernel

theorem qc_ok : (qc == ql.map Prod.fst) = true := by decide +kernel

theorem cov_ok0 : covOK s0 qc (bnd.getD 0 0) (bnd.getD 1 0) cov0 = true := by decide +kernel
theorem cov_ok1 : covOK s0 qc (bnd.getD 1 0) (bnd.getD 2 0) cov1 = true := by decide +kernel
theorem cov_ok2 : covOK s0 qc (bnd.getD 2 0) (bnd.getD 3 0) cov2 = true := by decide +kernel
theorem cov_ok3 : covOK s0 qc (bnd.getD 3 0) (bnd.getD 4 0) cov3 = true := by decide +kernel
theorem cov_ok4 : covOK s0 qc (bnd.getD 4 0) (bnd.getD 5 0) cov4 = true := by decide +kernel
theorem cov_ok5 : covOK s0 qc (bnd.getD 5 0) (bnd.getD 6 0) cov5 = true := by decide +kernel
theorem cov_ok6 : covOK s0 qc (bnd.getD 6 0) (bnd.getD 7 0) cov6 = true := by decide +kernel
theorem cov_ok7 : covOK s0 qc (bnd.getD 7 0) (bnd.getD 8 0) cov7 = true := by decide +kernel
theorem cov_ok8 : covOK s0 qc (bnd.getD 8 0) (bnd.getD 9 0) cov8 = true := by decide +kernel
theorem cov_ok9 : covOK s0 qc (bnd.getD 9 0) (bnd.getD 10 0) cov9 = true := by decide +kernel
theorem cov_ok10 : covOK s0 qc (bnd.getD 10 0) (bnd.getD 11 0) cov10 = true := by decide +kernel
theorem cov_ok11 : covOK s0 qc (bnd.getD 11 0) (bnd.getD 12 0) cov11 = true := by decide +kernel
theorem cov_ok12 : covOK s0 qc (bnd.getD 12 0) (bnd.getD 13 0) cov12 = true := by decide +kernel
theorem cov_ok13 : covOK s0 qc (bnd.getD 13 0) (bnd.getD 14 0) cov13 = true := by decide +kernel
theorem cov_ok14 : covOK s0 qc (bnd.getD 14 0) (bnd.getD 15 0) cov14 = true := by decide +kernel
theorem cov_ok15 : covOK s0 qc (bnd.getD 15 0) (bnd.getD 16 0) cov15 = true := by decide +kernel

theorem len_ok : (cov0.length + cov1.length + cov2.length + cov3.length + cov4.length +
    cov5.length + cov6.length + cov7.length + cov8.length + cov9.length + cov10.length +
    cov11.length + cov12.length + cov13.length + cov14.length + cov15.length == 7104) = true := by
  decide +kernel

end CFSG.KD.NPL587.Chk

end
