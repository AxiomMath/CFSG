module

public import Certificates.Data.Kernel.He7222.Chain
public import Certificates.Kernel.He7222.Data
public import Certificates.Kernel.He7222.TabData
public import Certificates.Kernel.He7222.Words
public import Certificates.Kernel.He7223.CentData
public import Certificates.Kernel.LocalComp.HeFix
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.OrbRow CFSG.KC.HeChain
  CertificateChecks.KernelLC.HeFix CertificateChecks.KernelHe7223

@[expose] noncomputable def trK (G : List Nat) (b : Nat) (R T : List Nat) : Bool :=
  treeK 8330 14 (mask 14) (pidn 8330 14) G b R T

@[expose] noncomputable def scK (G : List Nat) (b : Nat) (R T Ref Nn S : List Nat) : Bool :=
  schK 8330 14 (mask 14) G b R T Ref Nn S

theorem ch7222w : (wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (CW.getD 0 []) (getS a0G 0) &&
    wordEqK 8330 14 (mask 14) (pidn 8330 14) LU LUI 3 (CW.getD 1 []) (getS a0G 1) &&
    Nat.beq (lenS a0G) 2) = true := by
  quickRfl

theorem ch7222g1 : (Nat.beq (getS t1G 0) PC5 && Nat.beq (getS t1G 1) PC10 &&
    Nat.beq (lenS t1G) 2) = true := by
  quickRfl

theorem ch7222cm : (commAllK 8330 14 (mask 14) a0G (HG.F 0) &&
    commAllK 8330 14 (mask 14) t1G PT1) = true := by
  quickRfl

theorem ch7222a0t0 : trK a0G (getS a0Base 0) (getLs a0Tree 0) a0T0 = true := by quickRfl
theorem ch7222a0t1 : trK a0S1 (getS a0Base 1) (getLs a0Tree 1) a0T1 = true := by quickRfl
theorem ch7222a0t2 : trK a0S2 (getS a0Base 2) (getLs a0Tree 2) a0T2 = true := by quickRfl
theorem ch7222a0t3 : trK a0S3 (getS a0Base 3) (getLs a0Tree 3) a0T3 = true := by quickRfl
theorem ch7222a0t4 : trK a0S4 (getS a0Base 4) (getLs a0Tree 4) a0T4 = true := by quickRfl
theorem ch7222a0t5 : trK a0S5 (getS a0Base 5) (getLs a0Tree 5) a0T5 = true := by quickRfl
theorem ch7222a0t6 : trK a0S6 (getS a0Base 6) (getLs a0Tree 6) a0T6 = true := by quickRfl
theorem ch7222a0t7 : trK a0S7 (getS a0Base 7) (getLs a0Tree 7) a0T7 = true := by quickRfl

theorem ch7222a0s1 : scK a0G (getS a0Base 0) (getLs a0Tree 0) a0T0 (getLs a0LGens 1) a0N1 a0S1 =
    true := by quickRfl
theorem ch7222a0s2 : scK a0S1 (getS a0Base 1) (getLs a0Tree 1) a0T1 (getLs a0LGens 2) a0N2 a0S2 =
    true := by quickRfl
theorem ch7222a0s3 : scK a0S2 (getS a0Base 2) (getLs a0Tree 2) a0T2 (getLs a0LGens 3) a0N3 a0S3 =
    true := by quickRfl
theorem ch7222a0s4 : scK a0S3 (getS a0Base 3) (getLs a0Tree 3) a0T3 (getLs a0LGens 4) a0N4 a0S4 =
    true := by quickRfl
theorem ch7222a0s5 : scK a0S4 (getS a0Base 4) (getLs a0Tree 4) a0T4 (getLs a0LGens 5) a0N5 a0S5 =
    true := by quickRfl
theorem ch7222a0s6 : scK a0S5 (getS a0Base 5) (getLs a0Tree 5) a0T5 (getLs a0LGens 6) a0N6 a0S6 =
    true := by quickRfl
theorem ch7222a0s7 : scK a0S6 (getS a0Base 6) (getLs a0Tree 6) a0T6 (getLs a0LGens 7) a0N7 a0S7 =
    true := by quickRfl

theorem ch7222t1t0 : trK t1G (getS t1Base 0) (getLs t1Tree 0) t1T0 = true := by quickRfl
theorem ch7222t1t1 : trK t1S1 (getS t1Base 1) (getLs t1Tree 1) t1T1 = true := by quickRfl
theorem ch7222t1t2 : trK t1S2 (getS t1Base 2) (getLs t1Tree 2) t1T2 = true := by quickRfl
theorem ch7222t1t3 : trK t1S3 (getS t1Base 3) (getLs t1Tree 3) t1T3 = true := by quickRfl
theorem ch7222t1t4 : trK t1S4 (getS t1Base 4) (getLs t1Tree 4) t1T4 = true := by quickRfl
theorem ch7222t1t5 : trK t1S5 (getS t1Base 5) (getLs t1Tree 5) t1T5 = true := by quickRfl
theorem ch7222t1t6 : trK t1S6 (getS t1Base 6) (getLs t1Tree 6) t1T6 = true := by quickRfl

theorem ch7222t1s1 : scK t1G (getS t1Base 0) (getLs t1Tree 0) t1T0 (getLs t1LGens 1) t1N1 t1S1 =
    true := by quickRfl
theorem ch7222t1s2 : scK t1S1 (getS t1Base 1) (getLs t1Tree 1) t1T1 (getLs t1LGens 2) t1N2 t1S2 =
    true := by quickRfl
theorem ch7222t1s3 : scK t1S2 (getS t1Base 2) (getLs t1Tree 2) t1T2 (getLs t1LGens 3) t1N3 t1S3 =
    true := by quickRfl
theorem ch7222t1s4 : scK t1S3 (getS t1Base 3) (getLs t1Tree 3) t1T3 (getLs t1LGens 4) t1N4 t1S4 =
    true := by quickRfl
theorem ch7222t1s5 : scK t1S4 (getS t1Base 4) (getLs t1Tree 4) t1T4 (getLs t1LGens 5) t1N5 t1S5 =
    true := by quickRfl
theorem ch7222t1s6 : scK t1S5 (getS t1Base 5) (getLs t1Tree 5) t1T5 (getLs t1LGens 6) t1N6 t1S6 =
    true := by quickRfl

end CFSG.KD.He7222

end
