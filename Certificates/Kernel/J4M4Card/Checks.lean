module

public import Certificates.Data.Kernel.J4M4Card.Defs
public import Certificates.Kernel.J4NPVerdict.Defs
public import Certificates.Data.J4M4Card.Native
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M4Card

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.KD.J4M4F CFSG.KD.J4M4Card
  CFSG.Quasithin.KGC31.J4M4 CFSG.Quasithin.J4M4Card

@[expose] noncomputable def Us7256 : List Nat := [U0, U1, U2, U3, U4, U5, U6, U7, U8, U9, U10]

@[expose] noncomputable def FMs7256 : List Nat :=
  [FM_0, FM_1, FM_2, FM_3, FM_4, FM_5, FM_6, FM_7, FM_8, FM_9]

@[expose] noncomputable def G7256 : Nat := wordJ c rm one [A, B] [Ai, Bi] gWord

@[expose] noncomputable def Gi7256 : Nat := wordJ c rm one [A, B] [Ai, Bi] (invW gWord)

theorem t_ok : chkT () = true := by decide +kernel

theorem dist_ok : chkDistinct () = true := by decide +kernel

@[expose] noncomputable def mkK (T : List (List Nat)) (lo n : Nat) : Bool :=
  masksK c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] Us7256 schWord (fun i => invW (schWord i)) T lo n

theorem mk_ok0 : mkK maskTab 0 8 = true := by quickRfl
theorem mk_ok1 : mkK maskTab 8 8 = true := by quickRfl
theorem mk_ok2 : mkK maskTab 16 8 = true := by quickRfl
theorem mk_ok3 : mkK maskTab 24 8 = true := by quickRfl
theorem mk_ok4 : mkK maskTab 32 8 = true := by quickRfl
theorem mk_ok5 : mkK maskTab 40 8 = true := by quickRfl
theorem mk_ok6 : mkK maskTab 48 8 = true := by quickRfl
theorem mk_ok7 : mkK maskTab 56 6 = true := by quickRfl

@[expose] noncomputable def wtK (k j lo n : Nat) : Bool :=
  witChk c rm one G7256 Gi7256 Us7256 FMs7256 k j lo n

theorem wit_ok0 : wtK 2 0 0 128 = true := by quickRfl
theorem wit_ok1 : wtK 2 0 128 128 = true := by quickRfl
theorem wit_ok2 : wtK 2 0 256 128 = true := by quickRfl
theorem wit_ok3 : wtK 2 0 384 128 = true := by quickRfl
theorem wit_ok4 : wtK 2 0 512 128 = true := by quickRfl
theorem wit_ok5 : wtK 2 0 640 128 = true := by quickRfl
theorem wit_ok6 : wtK 2 0 768 128 = true := by quickRfl
theorem wit_ok7 : wtK 2 0 896 128 = true := by quickRfl

theorem ke_ok : keK c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] Us7256 keWords keMasks = true := by
  quickRfl

end CertificateChecks.KernelJ4M4Card

end
