module

public import Certificates.Kernel.EvenSporCocode.Data

public section

namespace CertificateChecks.KernelCocode

open CFSG.KC.EvenSporCocode CFSG.EvenSporadicStandard.Induction.Balance.Cocode24

set_option maxHeartbeats 0

theorem lt_eq : span sylowTabs = D.LT := by decide +kernel

theorem lt_len : D.LT.length = 1024 := by decide +kernel

theorem kt_nodup : D.KT.Nodup := by decide +kernel

theorem lt_valid : D.LT.all validB = true := by decide +kernel

theorem gens_valid : sylowTabs.all validB = true := by decide +kernel

theorem gens_aut : sylowTabs.all autOK = true := by decide +kernel

theorem kt_eq : D.LT.map encT = D.KT := by decide +kernel

theorem ep_eq : encAll D.LT = D.EP := by decide +kernel

theorem rb_len : D.RB.length = 32 := by decide +kernel

theorem close_ok : closeGo D.EP D.CB sylowTabs D.LT 0 = true := by decide +kernel

theorem iv_eq : invsK D.LT = D.IV := by decide +kernel

theorem iv_len : D.IV.length ≤ 16 * 12 := by decide +kernel

theorem planes_ok : planesB = true := by decide +kernel

end CertificateChecks.KernelCocode

end
