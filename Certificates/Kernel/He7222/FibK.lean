module

public import Certificates.Data.Kernel.He7222.Fib
public import Certificates.Kernel.He7222.ClsK
public import Certificates.Kernel.He7222.KData
public import Certificates.Kernel.He7222.FibData
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbRow CFSG.KC.HeChain

@[expose] noncomputable def a0KTs : List (List (List Nat)) :=
  [[a0K0T0, a0K0T1, a0K0T2, a0K0T3, a0K0T4, a0K0T5],
   [a0K1T0, a0K1T1, a0K1T2, a0K1T3, a0K1T4, a0K1T5]]

@[expose] noncomputable def a0KLs : List (List (List Nat)) :=
  [[a0K0T5, a0K0T4, a0K0T3, a0K0T2, a0K0T1, a0K0T0],
   [a0K1T5, a0K1T4, a0K1T3, a0K1T2, a0K1T1, a0K1T0]]

@[expose] noncomputable def t1KTs : List (List (List Nat)) :=
  [[t1K0T0, t1K0T1, t1K0T2, t1K0T3, t1K0T4], [t1K1T0, t1K1T1, t1K1T2, t1K1T3, t1K1T4],
   [t1K2T0, t1K2T1, t1K2T2, t1K2T3, t1K2T4],
   [t1K3T0, t1K3T1, t1K3T2, t1K3T3, t1K3T4, t1K3T5],
   [t1K4T0, t1K4T1, t1K4T2, t1K4T3, t1K4T4, t1K4T5]]

@[expose] noncomputable def t1KLs : List (List (List Nat)) :=
  [[t1K0T4, t1K0T3, t1K0T2, t1K0T1, t1K0T0], [t1K1T4, t1K1T3, t1K1T2, t1K1T1, t1K1T0],
   [t1K2T4, t1K2T3, t1K2T2, t1K2T1, t1K2T0],
   [t1K3T5, t1K3T4, t1K3T3, t1K3T2, t1K3T1, t1K3T0],
   [t1K4T5, t1K4T4, t1K4T3, t1K4T2, t1K4T1, t1K4T0]]

@[expose] noncomputable def srA (j : Nat) : Bool :=
  srK 14 (mask 14) a0Ts a0TIs (getLL a0KTs j) (stkK a0Ts (getLs a0RT (getS a0SRep j)))
    (getS scH j) (getS scHI j) (lenS (getLs a0XR j)) (getLL a0KC (getS a0SRep j)) (getLs a0XR j)
    (getLs a0Sv j) (getLL a0SR j)

@[expose] noncomputable def srT (j : Nat) : Bool :=
  srK 14 (mask 14) t1Ts t1TIs (getLL t1KTs j) (stkK t1Ts (getLs t1RT (getS t1SRep j)))
    (getS scH (Nat.add 3 j)) (getS scHI (Nat.add 3 j)) (lenS (getLs t1XR j))
    (getLL t1KC (getS t1SRep j)) (getLs t1XR j) (getLs t1Sv j) (getLL t1SR j)

@[expose] noncomputable def fbA (i : Nat) : Bool :=
  strictB (getS (getLs a0FI i) 0) (fun j => strictB (getS (getLs a0FI i) 1) (fun r =>
    fibK 14 (mask 14) (getLL a0KTs j) (getLL a0KLs j)
      (List.cons (getS scH j)
        (stkK a0Ts (getLs (getLL a0KC (getS a0SRep j)) (getS (getLs a0XR j) r))))
      (getLL a0FR i) (getLL a0FT i)))

@[expose] noncomputable def fbT (i : Nat) : Bool :=
  strictB (getS (getLs t1FI i) 0) (fun j => strictB (getS (getLs t1FI i) 1) (fun r =>
    fibK 14 (mask 14) (getLL t1KTs j) (getLL t1KLs j)
      (List.cons (getS scH (Nat.add 3 j))
        (stkK t1Ts (getLs (getLL t1KC (getS t1SRep j)) (getS (getLs t1XR j) r))))
      (getLL t1FR i) (getLL t1FT i)))

theorem ch7222sra0 : srA 0 = true := by quickRfl
theorem ch7222sra1 : srA 1 = true := by quickRfl
theorem ch7222srt0 : srT 0 = true := by quickRfl
theorem ch7222srt1 : srT 1 = true := by quickRfl
theorem ch7222srt2 : srT 2 = true := by quickRfl
theorem ch7222srt3 : srT 3 = true := by quickRfl
theorem ch7222srt4 : srT 4 = true := by quickRfl

theorem ch7222fba : ∀ i < 10, fbA i = true := by kc_cover 1

theorem ch7222fbt : ∀ i < 44, fbT i = true := by kc_cover 2

end CFSG.KD.He7222

end
