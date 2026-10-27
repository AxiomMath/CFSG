
module

public import Certificates.Kernel.MonsterB.Fischer3065T
public import Certificates.Kernel.MonsterB.Fischer3067B
public import Certificates.Kernel.MonsterB.FischerTabs

set_option maxRecDepth 400000
set_option maxHeartbeats 0

public section

namespace CertificateChecks.KernelMonB.FNeg

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.KC.FischerK
  CFSG.KC.FischerE CFSG.KC.FischerB CertificateChecks.KernelMonB.F3067 CertificateChecks.KernelMonB.F3065
  CertificateChecks.KernelMonB.FischerTabs

theorem neg_rank : (!spanT ad949 23) = true := by decide +kernel

theorem neg_rank_hi : (!spanT (2 ^ 78 :: ad949.tail) 22) = true := by decide +kernel

theorem neg_inv : (!invChk 13) = true := by decide +kernel

theorem neg_orb : (!orbChkB (mkB 1 11, mkB 0 11, mkB 0 11, mkB 0 11)) = true := by
  decide +kernel

theorem neg_table : (!(List.range 78).all fun j => tableEntryT (labelWord 1) 0 j) = true := by
  decide +kernel

theorem neg_supp : (!suppT (labelWord 0) (ncL 0 ^^^ 1)) = true := by decide +kernel

theorem neg_col :
    (!(vecMulL FD.GT (GramLit.rowCoords[5]!) ^^^ 1 == colN GramLit.ncRows 5)) = true := by
  decide +kernel

end CertificateChecks.KernelMonB.FNeg

end
