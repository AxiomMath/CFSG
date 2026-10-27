module

public import Certificates.Data.Kernel.FzUT.BFacts
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KC.FzBMod

theorem ch441796_small (c : Bool) : smallB c = true := by cases c <;> quickRfl

theorem ch441796_cardM : Nat.beq (countN 1024 (fun x => Nat.beq (x / 64 % 2) 0)) 512 = true := by
  quickRfl

theorem ch441796_mmul : mMulB = true := by quickRfl

theorem ch441796_msq : mSqB = true := by quickRfl

theorem ch441796_f3_1 (c : Bool) : f3B c 1 = true := by cases c <;> quickRfl

theorem ch441796_f3_2 (c : Bool) : f3B c 2 = true := by cases c <;> quickRfl

theorem ch441796_f3_3 (c : Bool) : f3B c 3 = true := by cases c <;> quickRfl

theorem ch441796_v2 (c : Bool) : v2B c = true := by cases c <;> quickRfl

theorem ch441796_w0 (c : Bool) : w0B c = true := by cases c <;> quickRfl

theorem ch441796_e32_1 : e32B e32L1 = true := by quickRfl

theorem ch441796_e32_2 : e32B e32L2 = true := by quickRfl

theorem ch441796_h1 : h1B = true := by quickRfl

theorem ch441796_v1 : v1B = true := by quickRfl

end CFSG.KC.FzBMod
