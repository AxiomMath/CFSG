module

public import Certificates.Data.Kernel.FF81Forms
public import Certificates.Kernel.FF81Forms.Data

public section

namespace CFSG.KD.FF81F

open CFSG.KC.FF81F

set_option maxRecDepth 100000

theorem ch799700_pairs : allPairs PK = true := by decide +kernel

theorem ch799700_l0 : Nat.beq (lenK t0) 1024 = true := by decide +kernel
theorem ch799700_l1 : Nat.beq (lenK t1) 1024 = true := by decide +kernel
theorem ch799700_l2 : Nat.beq (lenK t2) 1024 = true := by decide +kernel
theorem ch799700_l3 : Nat.beq (lenK t3) 1024 = true := by decide +kernel
theorem ch799700_l4 : Nat.beq (lenK t4) 1024 = true := by decide +kernel
theorem ch799700_l5 : Nat.beq (lenK t5) 1024 = true := by decide +kernel
theorem ch799700_l6 : Nat.beq (lenK t6) 1024 = true := by decide +kernel
theorem ch799700_l7 : Nat.beq (lenK t7) 1024 = true := by decide +kernel
theorem ch799700_l8 : Nat.beq (lenK t8) 1024 = true := by decide +kernel
theorem ch799700_l9 : Nat.beq (lenK t9) 1024 = true := by decide +kernel
theorem ch799700_l10 : Nat.beq (lenK t10) 1024 = true := by decide +kernel
theorem ch799700_l11 : Nat.beq (lenK t11) 1024 = true := by decide +kernel
theorem ch799700_l12 : Nat.beq (lenK t12) 1024 = true := by decide +kernel
theorem ch799700_l13 : Nat.beq (lenK t13) 1024 = true := by decide +kernel
theorem ch799700_l14 : Nat.beq (lenK t14) 1024 = true := by decide +kernel
theorem ch799700_l15 : Nat.beq (lenK t15) 1024 = true := by decide +kernel
theorem ch799700_l16 : Nat.beq (lenK t16) 1024 = true := by decide +kernel
theorem ch799700_l17 : Nat.beq (lenK t17) 1024 = true := by decide +kernel
theorem ch799700_l18 : Nat.beq (lenK t18) 1024 = true := by decide +kernel
theorem ch799700_l19 : Nat.beq (lenK t19) 1024 = true := by decide +kernel
theorem ch799700_l20 : Nat.beq (lenK t20) 1024 = true := by decide +kernel
theorem ch799700_l21 : Nat.beq (lenK t21) 1024 = true := by decide +kernel
theorem ch799700_l22 : Nat.beq (lenK t22) 1024 = true := by decide +kernel
theorem ch799700_l23 : Nat.beq (lenK t23) 1024 = true := by decide +kernel
theorem ch799700_l24 : Nat.beq (lenK t24) 1024 = true := by decide +kernel
theorem ch799700_l25 : Nat.beq (lenK t25) 1024 = true := by decide +kernel
theorem ch799700_l26 : Nat.beq (lenK t26) 1024 = true := by decide +kernel
theorem ch799700_l27 : Nat.beq (lenK t27) 1024 = true := by decide +kernel
theorem ch799700_l28 : Nat.beq (lenK t28) 1024 = true := by decide +kernel
theorem ch799700_l29 : Nat.beq (lenK t29) 1024 = true := by decide +kernel
theorem ch799700_l30 : Nat.beq (lenK t30) 1024 = true := by decide +kernel
theorem ch799700_l31 : Nat.beq (lenK t31) 1024 = true := by decide +kernel

theorem ch799700_w0 : walkK PK 0 t0 = true := by decide +kernel
theorem ch799700_w1 : walkK PK 1024 t1 = true := by decide +kernel
theorem ch799700_w2 : walkK PK 2048 t2 = true := by decide +kernel
theorem ch799700_w3 : walkK PK 3072 t3 = true := by decide +kernel
theorem ch799700_w4 : walkK PK 4096 t4 = true := by decide +kernel
theorem ch799700_w5 : walkK PK 5120 t5 = true := by decide +kernel
theorem ch799700_w6 : walkK PK 6144 t6 = true := by decide +kernel
theorem ch799700_w7 : walkK PK 7168 t7 = true := by decide +kernel
theorem ch799700_w8 : walkK PK 8192 t8 = true := by decide +kernel
theorem ch799700_w9 : walkK PK 9216 t9 = true := by decide +kernel
theorem ch799700_w10 : walkK PK 10240 t10 = true := by decide +kernel
theorem ch799700_w11 : walkK PK 11264 t11 = true := by decide +kernel
theorem ch799700_w12 : walkK PK 12288 t12 = true := by decide +kernel
theorem ch799700_w13 : walkK PK 13312 t13 = true := by decide +kernel
theorem ch799700_w14 : walkK PK 14336 t14 = true := by decide +kernel
theorem ch799700_w15 : walkK PK 15360 t15 = true := by decide +kernel
theorem ch799700_w16 : walkK PK 16384 t16 = true := by decide +kernel
theorem ch799700_w17 : walkK PK 17408 t17 = true := by decide +kernel
theorem ch799700_w18 : walkK PK 18432 t18 = true := by decide +kernel
theorem ch799700_w19 : walkK PK 19456 t19 = true := by decide +kernel
theorem ch799700_w20 : walkK PK 20480 t20 = true := by decide +kernel
theorem ch799700_w21 : walkK PK 21504 t21 = true := by decide +kernel
theorem ch799700_w22 : walkK PK 22528 t22 = true := by decide +kernel
theorem ch799700_w23 : walkK PK 23552 t23 = true := by decide +kernel
theorem ch799700_w24 : walkK PK 24576 t24 = true := by decide +kernel
theorem ch799700_w25 : walkK PK 25600 t25 = true := by decide +kernel
theorem ch799700_w26 : walkK PK 26624 t26 = true := by decide +kernel
theorem ch799700_w27 : walkK PK 27648 t27 = true := by decide +kernel
theorem ch799700_w28 : walkK PK 28672 t28 = true := by decide +kernel
theorem ch799700_w29 : walkK PK 29696 t29 = true := by decide +kernel
theorem ch799700_w30 : walkK PK 30720 t30 = true := by decide +kernel
theorem ch799700_w31 : walkK PK 31744 t31 = true := by decide +kernel

end CFSG.KD.FF81F
