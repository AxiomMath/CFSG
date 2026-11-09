module

public import Certificates.Kernel.Sporadic.ONL37.Seg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.ONL37

#kc_natval W4v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 122) (chunkW (nat_lit 4))) (preC (nat_lit 4))

theorem l37Wch4_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 122) (chunkW (nat_lit 4))) (preC (nat_lit 4))) W4v1 = true := by
  quickRfl

#kc_natval W4v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 122) (List.drop (nat_lit 122) (chunkW (nat_lit 4)))) W4v1

theorem l37Wch4_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 122) (List.drop (nat_lit 122) (chunkW (nat_lit 4)))) W4v1) W4v2 = true := by
  quickRfl

#kc_natval W4v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 121) (List.drop (nat_lit 244) (chunkW (nat_lit 4)))) W4v2

theorem l37Wch4_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 121) (List.drop (nat_lit 244) (chunkW (nat_lit 4)))) W4v2) W4v3 = true := by
  quickRfl

theorem l37Wch4_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 365) (chunkW (nat_lit 4))) W4v3) (ipC (nat_lit 4)) = true := by
  quickRfl

theorem l37Wch4 : l37Wch (nat_lit 4) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 4)) (nat_lit 122) _ _ l37Wch4_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 4)) (nat_lit 122) (nat_lit 122) (nat_lit 244) _ _ rfl l37Wch4_p1).trans (wordK_seg _ _ (chunkW (nat_lit 4)) (nat_lit 244) (nat_lit 121) (nat_lit 365) _ _ rfl l37Wch4_p2)))
    l37Wch4_p3)

#kc_natval W5v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 122) (chunkW (nat_lit 5))) (preC (nat_lit 5))

theorem l37Wch5_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 122) (chunkW (nat_lit 5))) (preC (nat_lit 5))) W5v1 = true := by
  quickRfl

#kc_natval W5v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 122) (List.drop (nat_lit 122) (chunkW (nat_lit 5)))) W5v1

theorem l37Wch5_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 122) (List.drop (nat_lit 122) (chunkW (nat_lit 5)))) W5v1) W5v2 = true := by
  quickRfl

#kc_natval W5v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 121) (List.drop (nat_lit 244) (chunkW (nat_lit 5)))) W5v2

theorem l37Wch5_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 121) (List.drop (nat_lit 244) (chunkW (nat_lit 5)))) W5v2) W5v3 = true := by
  quickRfl

theorem l37Wch5_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 365) (chunkW (nat_lit 5))) W5v3) (ipC (nat_lit 5)) = true := by
  quickRfl

theorem l37Wch5 : l37Wch (nat_lit 5) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 5)) (nat_lit 122) _ _ l37Wch5_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 5)) (nat_lit 122) (nat_lit 122) (nat_lit 244) _ _ rfl l37Wch5_p1).trans (wordK_seg _ _ (chunkW (nat_lit 5)) (nat_lit 244) (nat_lit 121) (nat_lit 365) _ _ rfl l37Wch5_p2)))
    l37Wch5_p3)

#kc_natval W6v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (chunkW (nat_lit 6))) (preC (nat_lit 6))

theorem l37Wch6_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (chunkW (nat_lit 6))) (preC (nat_lit 6))) W6v1 = true := by
  quickRfl

#kc_natval W6v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (List.drop (nat_lit 117) (chunkW (nat_lit 6)))) W6v1

theorem l37Wch6_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (List.drop (nat_lit 117) (chunkW (nat_lit 6)))) W6v1) W6v2 = true := by
  quickRfl

#kc_natval W6v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (List.drop (nat_lit 234) (chunkW (nat_lit 6)))) W6v2

theorem l37Wch6_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (List.drop (nat_lit 234) (chunkW (nat_lit 6)))) W6v2) W6v3 = true := by
  quickRfl

#kc_natval W6v4 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 116) (List.drop (nat_lit 351) (chunkW (nat_lit 6)))) W6v3

theorem l37Wch6_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 116) (List.drop (nat_lit 351) (chunkW (nat_lit 6)))) W6v3) W6v4 = true := by
  quickRfl

theorem l37Wch6_p4 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 467) (chunkW (nat_lit 6))) W6v4) (ipC (nat_lit 6)) = true := by
  quickRfl

theorem l37Wch6 : l37Wch (nat_lit 6) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 6)) (nat_lit 117) _ _ l37Wch6_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 6)) (nat_lit 117) (nat_lit 117) (nat_lit 234) _ _ rfl l37Wch6_p1).trans ((wordK_seg _ _ (chunkW (nat_lit 6)) (nat_lit 234) (nat_lit 117) (nat_lit 351) _ _ rfl l37Wch6_p2).trans (wordK_seg _ _ (chunkW (nat_lit 6)) (nat_lit 351) (nat_lit 116) (nat_lit 467) _ _ rfl l37Wch6_p3))))
    l37Wch6_p4)

#kc_natval W7v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 140) (chunkW (nat_lit 7))) (preC (nat_lit 7))

theorem l37Wch7_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 140) (chunkW (nat_lit 7))) (preC (nat_lit 7))) W7v1 = true := by
  quickRfl

#kc_natval W7v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 139) (List.drop (nat_lit 140) (chunkW (nat_lit 7)))) W7v1

theorem l37Wch7_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 139) (List.drop (nat_lit 140) (chunkW (nat_lit 7)))) W7v1) W7v2 = true := by
  quickRfl

#kc_natval W7v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 139) (List.drop (nat_lit 279) (chunkW (nat_lit 7)))) W7v2

theorem l37Wch7_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 139) (List.drop (nat_lit 279) (chunkW (nat_lit 7)))) W7v2) W7v3 = true := by
  quickRfl

theorem l37Wch7_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 418) (chunkW (nat_lit 7))) W7v3) (ipC (nat_lit 7)) = true := by
  quickRfl

theorem l37Wch7 : l37Wch (nat_lit 7) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 7)) (nat_lit 140) _ _ l37Wch7_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 7)) (nat_lit 140) (nat_lit 139) (nat_lit 279) _ _ rfl l37Wch7_p1).trans (wordK_seg _ _ (chunkW (nat_lit 7)) (nat_lit 279) (nat_lit 139) (nat_lit 418) _ _ rfl l37Wch7_p2)))
    l37Wch7_p3)

end CertificateChecks.KernelSpor.ONL37

end
