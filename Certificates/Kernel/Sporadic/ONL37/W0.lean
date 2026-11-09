module

public import Certificates.Kernel.Sporadic.ONL37.Seg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.ONL37

#kc_natval W0v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 107) (chunkW (nat_lit 0))) (preC (nat_lit 0))

theorem l37Wch0_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 107) (chunkW (nat_lit 0))) (preC (nat_lit 0))) W0v1 = true := by
  quickRfl

#kc_natval W0v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 106) (List.drop (nat_lit 107) (chunkW (nat_lit 0)))) W0v1

theorem l37Wch0_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 106) (List.drop (nat_lit 107) (chunkW (nat_lit 0)))) W0v1) W0v2 = true := by
  quickRfl

#kc_natval W0v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 106) (List.drop (nat_lit 213) (chunkW (nat_lit 0)))) W0v2

theorem l37Wch0_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 106) (List.drop (nat_lit 213) (chunkW (nat_lit 0)))) W0v2) W0v3 = true := by
  quickRfl

theorem l37Wch0_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 319) (chunkW (nat_lit 0))) W0v3) (ipC (nat_lit 0)) = true := by
  quickRfl

theorem l37Wch0 : l37Wch (nat_lit 0) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 0)) (nat_lit 107) _ _ l37Wch0_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 0)) (nat_lit 107) (nat_lit 106) (nat_lit 213) _ _ rfl l37Wch0_p1).trans (wordK_seg _ _ (chunkW (nat_lit 0)) (nat_lit 213) (nat_lit 106) (nat_lit 319) _ _ rfl l37Wch0_p2)))
    l37Wch0_p3)

end CertificateChecks.KernelSpor.ONL37

end
