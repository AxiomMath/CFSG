module

public import Certificates.Data.Kernel.He7222.KChain
public import Certificates.Kernel.He7222.FixK
public import Certificates.Kernel.He7222.Data
public import Certificates.Kernel.He7222.KData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain

@[expose] noncomputable def kg0 (j : Nat) (G : List Nat) : Bool :=
  kgK 8330 14 (mask 14) (pidn 8330 14) a0Ts (rep0 (getS a0SRep j)) G (getLL a0KU j)

@[expose] noncomputable def kg1 (j : Nat) (G : List Nat) : Bool :=
  kgK 8330 14 (mask 14) (pidn 8330 14) t1Ts (rep1 (getS t1SRep j)) G (getLL t1KU j)

@[expose] noncomputable def kc0 (j : Nat) (G : List Nat) (T S Nn : List (List Nat)) : Bool :=
  chainK 8330 14 (mask 14) (pidn 8330 14) G (getLs a0QBase j) (getLL a0QTree j) T S
    (getLL a0QLGens j) Nn

@[expose] noncomputable def kc1 (j : Nat) (G : List Nat) (T S Nn : List (List Nat)) : Bool :=
  chainK 8330 14 (mask 14) (pidn 8330 14) G (getLs t1QBase j) (getLL t1QTree j) T S
    (getLL t1QLGens j) Nn

theorem ch7222kga0 : kg0 0 a0K0G = true := by quickRfl
theorem ch7222kga1 : kg0 1 a0K1G = true := by quickRfl
theorem ch7222kgt0 : kg1 0 t1K0G = true := by quickRfl
theorem ch7222kgt1 : kg1 1 t1K1G = true := by quickRfl
theorem ch7222kgt2 : kg1 2 t1K2G = true := by quickRfl
theorem ch7222kgt3 : kg1 3 t1K3G = true := by quickRfl
theorem ch7222kgt4 : kg1 4 t1K4G = true := by quickRfl

theorem ch7222kca0 : kc0 0 a0K0G [a0K0T0, a0K0T1, a0K0T2, a0K0T3, a0K0T4, a0K0T5]
    [a0K0S1, a0K0S2, a0K0S3, a0K0S4, a0K0S5] [a0K0N1, a0K0N2, a0K0N3, a0K0N4, a0K0N5] = true := by
  quickRfl

theorem ch7222kca1 : kc0 1 a0K1G [a0K1T0, a0K1T1, a0K1T2, a0K1T3, a0K1T4, a0K1T5]
    [a0K1S1, a0K1S2, a0K1S3, a0K1S4, a0K1S5] [a0K1N1, a0K1N2, a0K1N3, a0K1N4, a0K1N5] = true := by
  quickRfl

theorem ch7222kct0 : kc1 0 t1K0G [t1K0T0, t1K0T1, t1K0T2, t1K0T3, t1K0T4]
    [t1K0S1, t1K0S2, t1K0S3, t1K0S4] [t1K0N1, t1K0N2, t1K0N3, t1K0N4] = true := by
  quickRfl

theorem ch7222kct1 : kc1 1 t1K1G [t1K1T0, t1K1T1, t1K1T2, t1K1T3, t1K1T4]
    [t1K1S1, t1K1S2, t1K1S3, t1K1S4] [t1K1N1, t1K1N2, t1K1N3, t1K1N4] = true := by
  quickRfl

theorem ch7222kct2 : kc1 2 t1K2G [t1K2T0, t1K2T1, t1K2T2, t1K2T3, t1K2T4]
    [t1K2S1, t1K2S2, t1K2S3, t1K2S4] [t1K2N1, t1K2N2, t1K2N3, t1K2N4] = true := by
  quickRfl

theorem ch7222kct3 : kc1 3 t1K3G [t1K3T0, t1K3T1, t1K3T2, t1K3T3, t1K3T4, t1K3T5]
    [t1K3S1, t1K3S2, t1K3S3, t1K3S4, t1K3S5] [t1K3N1, t1K3N2, t1K3N3, t1K3N4, t1K3N5] = true := by
  quickRfl

theorem ch7222kct4 : kc1 4 t1K4G [t1K4T0, t1K4T1, t1K4T2, t1K4T3, t1K4T4, t1K4T5]
    [t1K4S1, t1K4S2, t1K4S3, t1K4S4, t1K4S5] [t1K4N1, t1K4N2, t1K4N3, t1K4N4, t1K4N5] = true := by
  quickRfl

end CFSG.KD.He7222

end
