module

public import Certificates.Data.Kernel.He7222.Cls
public import Certificates.Kernel.He7222.TabData
public import Certificates.Kernel.He7222.HData
public import Certificates.Kernel.He7222.InvData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.He7222

open CFSG.KC.Enum CFSG.KS CFSG.KC.HeChain

@[expose] noncomputable def ivK (T TI : List Nat) : Bool := invLK 8330 14 (mask 14) (pidn 8330 14) T TI

theorem ch7222ia0 : ivK a0T0 a0TI0 = true := by quickRfl
theorem ch7222ia1 : ivK a0T1 a0TI1 = true := by quickRfl
theorem ch7222ia2 : ivK a0T2 a0TI2 = true := by quickRfl
theorem ch7222ia3 : ivK a0T3 a0TI3 = true := by quickRfl
theorem ch7222ia4 : ivK a0T4 a0TI4 = true := by quickRfl
theorem ch7222ia5 : ivK a0T5 a0TI5 = true := by quickRfl
theorem ch7222ia6 : ivK a0T6 a0TI6 = true := by quickRfl
theorem ch7222ia7 : ivK a0T7 a0TI7 = true := by quickRfl
theorem ch7222it0 : ivK t1T0 t1TI0 = true := by quickRfl
theorem ch7222it1 : ivK t1T1 t1TI1 = true := by quickRfl
theorem ch7222it2 : ivK t1T2 t1TI2 = true := by quickRfl
theorem ch7222it3 : ivK t1T3 t1TI3 = true := by quickRfl
theorem ch7222it4 : ivK t1T4 t1TI4 = true := by quickRfl
theorem ch7222it5 : ivK t1T5 t1TI5 = true := by quickRfl
theorem ch7222it6 : ivK t1T6 t1TI6 = true := by quickRfl
theorem ch7222ih : ivK scH scHI = true := by quickRfl

end CFSG.KD.He7222

end
