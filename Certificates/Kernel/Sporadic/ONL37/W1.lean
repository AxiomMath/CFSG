module

public import Certificates.Kernel.Sporadic.ONL37.Seg
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CertificateChecks.KernelSpor.ONL37

#kc_natval W1v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (chunkW (nat_lit 1))) (preC (nat_lit 1))

theorem l37Wch1_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (chunkW (nat_lit 1))) (preC (nat_lit 1))) W1v1 = true := by
  quickRfl

#kc_natval W1v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (List.drop (nat_lit 117) (chunkW (nat_lit 1)))) W1v1

theorem l37Wch1_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (List.drop (nat_lit 117) (chunkW (nat_lit 1)))) W1v1) W1v2 = true := by
  quickRfl

#kc_natval W1v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (List.drop (nat_lit 234) (chunkW (nat_lit 1)))) W1v2

theorem l37Wch1_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (List.drop (nat_lit 234) (chunkW (nat_lit 1)))) W1v2) W1v3 = true := by
  quickRfl

#kc_natval W1v4 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 117) (List.drop (nat_lit 351) (chunkW (nat_lit 1)))) W1v3

theorem l37Wch1_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 117) (List.drop (nat_lit 351) (chunkW (nat_lit 1)))) W1v3) W1v4 = true := by
  quickRfl

theorem l37Wch1_p4 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 468) (chunkW (nat_lit 1))) W1v4) (ipC (nat_lit 1)) = true := by
  quickRfl

theorem l37Wch1 : l37Wch (nat_lit 1) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 1)) (nat_lit 117) _ _ l37Wch1_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 1)) (nat_lit 117) (nat_lit 117) (nat_lit 234) _ _ rfl l37Wch1_p1).trans ((wordK_seg _ _ (chunkW (nat_lit 1)) (nat_lit 234) (nat_lit 117) (nat_lit 351) _ _ rfl l37Wch1_p2).trans (wordK_seg _ _ (chunkW (nat_lit 1)) (nat_lit 351) (nat_lit 117) (nat_lit 468) _ _ rfl l37Wch1_p3))))
    l37Wch1_p4)

#kc_natval W2v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 126) (chunkW (nat_lit 2))) (preC (nat_lit 2))

theorem l37Wch2_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 126) (chunkW (nat_lit 2))) (preC (nat_lit 2))) W2v1 = true := by
  quickRfl

#kc_natval W2v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 126) (List.drop (nat_lit 126) (chunkW (nat_lit 2)))) W2v1

theorem l37Wch2_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 126) (List.drop (nat_lit 126) (chunkW (nat_lit 2)))) W2v1) W2v2 = true := by
  quickRfl

#kc_natval W2v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 126) (List.drop (nat_lit 252) (chunkW (nat_lit 2)))) W2v2

theorem l37Wch2_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 126) (List.drop (nat_lit 252) (chunkW (nat_lit 2)))) W2v2) W2v3 = true := by
  quickRfl

#kc_natval W2v4 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 125) (List.drop (nat_lit 378) (chunkW (nat_lit 2)))) W2v3

theorem l37Wch2_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 125) (List.drop (nat_lit 378) (chunkW (nat_lit 2)))) W2v3) W2v4 = true := by
  quickRfl

theorem l37Wch2_p4 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 503) (chunkW (nat_lit 2))) W2v4) (ipC (nat_lit 2)) = true := by
  quickRfl

theorem l37Wch2 : l37Wch (nat_lit 2) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 2)) (nat_lit 126) _ _ l37Wch2_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 2)) (nat_lit 126) (nat_lit 126) (nat_lit 252) _ _ rfl l37Wch2_p1).trans ((wordK_seg _ _ (chunkW (nat_lit 2)) (nat_lit 252) (nat_lit 126) (nat_lit 378) _ _ rfl l37Wch2_p2).trans (wordK_seg _ _ (chunkW (nat_lit 2)) (nat_lit 378) (nat_lit 125) (nat_lit 503) _ _ rfl l37Wch2_p3))))
    l37Wch2_p4)

#kc_natval W3v1 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 118) (chunkW (nat_lit 3))) (preC (nat_lit 3))

theorem l37Wch3_p0 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 118) (chunkW (nat_lit 3))) (preC (nat_lit 3))) W3v1 = true := by
  quickRfl

#kc_natval W3v2 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 118) (List.drop (nat_lit 118) (chunkW (nat_lit 3)))) W3v1

theorem l37Wch3_p1 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 118) (List.drop (nat_lit 118) (chunkW (nat_lit 3)))) W3v1) W3v2 = true := by
  quickRfl

#kc_natval W3v3 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 118) (List.drop (nat_lit 236) (chunkW (nat_lit 3)))) W3v2

theorem l37Wch3_p2 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 118) (List.drop (nat_lit 236) (chunkW (nat_lit 3)))) W3v2) W3v3 = true := by
  quickRfl

#kc_natval W3v4 := CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
  (List.take (nat_lit 118) (List.drop (nat_lit 354) (chunkW (nat_lit 3)))) W3v3

theorem l37Wch3_p3 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.take (nat_lit 118) (List.drop (nat_lit 354) (chunkW (nat_lit 3)))) W3v3) W3v4 = true := by
  quickRfl

theorem l37Wch3_p4 : Nat.beq (CFSG.KS.ONC.wordK (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM) (CFSG.KS.ONC.seedL SA SA SB SBI)
    (List.drop (nat_lit 472) (chunkW (nat_lit 3))) W3v4) (ipC (nat_lit 3)) = true := by
  quickRfl

theorem l37Wch3 : l37Wch (nat_lit 3) = true :=
  chunkK_of sA sB sBI sa1 sb1 (beq_of_eq' ((wordK_seg0 _ _ (chunkW (nat_lit 3)) (nat_lit 118) _ _ l37Wch3_p0).trans ((wordK_seg _ _ (chunkW (nat_lit 3)) (nat_lit 118) (nat_lit 118) (nat_lit 236) _ _ rfl l37Wch3_p1).trans ((wordK_seg _ _ (chunkW (nat_lit 3)) (nat_lit 236) (nat_lit 118) (nat_lit 354) _ _ rfl l37Wch3_p2).trans (wordK_seg _ _ (chunkW (nat_lit 3)) (nat_lit 354) (nat_lit 118) (nat_lit 472) _ _ rfl l37Wch3_p3))))
    l37Wch3_p4)

end CertificateChecks.KernelSpor.ONL37

end
