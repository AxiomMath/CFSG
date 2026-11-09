module

public import Certificates.Data.Kernel.He7222.Cls
public import Certificates.Kernel.He7222.TabData
public import Certificates.Kernel.He7222.HData
public import Certificates.Kernel.He7222.InvData
public import Certificates.Kernel.He7222.PcC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.HeChain

@[expose] noncomputable def ivK (T TI : List Nat) : Bool := invLK 8330 14 (mask 14) (pidn 8330 14) T TI

theorem ivK_C (T TI : List Nat) : ivK T TI = invLKC 8330 14 (mask 14) (pidn 8330 14) T TI :=
  invLK_C _ _ _ _ _

theorem ch7222ia0_0 :
    invAllC 8330 14 (mask 14) (pidn 8330 14) a0TI0 (a0T0.take 35) 0 = true := by quickRfl

theorem ch7222ia0_1 :
    invAllC 8330 14 (mask 14) (pidn 8330 14) a0TI0 ((a0T0.drop 35).take 35)
      (0 + (a0T0.take 35).length) = true := by quickRfl

theorem ch7222ia0_2 :
    invFromC 8330 14 (mask 14) (pidn 8330 14) a0TI0 ((a0T0.drop 35).drop 35)
      (0 + (a0T0.take 35).length + ((a0T0.drop 35).take 35).length) = true := by quickRfl

theorem ch7222ia0 : ivK a0T0 a0TI0 = true := by
  rw [ivK_C, invLKC_from, ← List.take_append_drop 35 a0T0, invFromC_append,
    ← List.take_append_drop 35 (a0T0.drop 35), invFromC_append, ch7222ia0_0, ch7222ia0_1,
    Nat.add_assoc, ← Nat.add_assoc 0, ch7222ia0_2]
  rfl
theorem ch7222ia1 : ivK a0T1 a0TI1 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ia2 : ivK a0T2 a0TI2 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ia3 : ivK a0T3 a0TI3 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ia4 : ivK a0T4 a0TI4 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ia5 : ivK a0T5 a0TI5 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ia6 : ivK a0T6 a0TI6 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ia7 : ivK a0T7 a0TI7 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it0 : ivK t1T0 t1TI0 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it1 : ivK t1T1 t1TI1 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it2 : ivK t1T2 t1TI2 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it3 : ivK t1T3 t1TI3 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it4 : ivK t1T4 t1TI4 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it5 : ivK t1T5 t1TI5 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222it6 : ivK t1T6 t1TI6 = true := (ivK_C _ _).trans (by quickRfl)
theorem ch7222ih : ivK scH scHI = true := (ivK_C _ _).trans (by quickRfl)

end CFSG.KD.He7222

end
