module

public import Certificates.Kernel.SporSch.PairBT.J2F67Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J2F67Chk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J2F67

@[expose] noncomputable def P2 : Nat := pcomp 315 9 (mask 9) R1 R1

@[expose] noncomputable def P3 : Nat := pcomp 315 9 (mask 9) R1 P2

@[expose] noncomputable def P4 : Nat := pcomp 315 9 (mask 9) R1 P3

theorem sz : szOK 315 9 = true := by quickRfl

theorem ord0 : Nat.beq (ordK PJ2.LR 3) 604800 = true := by quickRfl

theorem ord : ordK PJ2.LR 3 = 604800 := Nat.eq_of_beq_eq_true ord0

theorem c1 : canonK 315 9 (mask 9) (315 * 9) R1 = true := by quickRfl
theorem c2 : canonK 315 9 (mask 9) (315 * 9) R2 = true := by quickRfl
theorem c3 : canonK 315 9 (mask 9) (315 * 9) R3 = true := by quickRfl
theorem c4 : canonK 315 9 (mask 9) (315 * 9) R4 = true := by quickRfl
theorem c7 : canonK 315 9 (mask 9) (315 * 9) Z7 = true := by quickRfl

theorem s1 : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 R1 = true := by
  quickRfl
theorem s2 : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 R2 = true := by
  quickRfl
theorem s3 : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 R3 = true := by
  quickRfl
theorem s4 : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 R4 = true := by
  quickRfl
theorem s7 : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 Z7 = true := by
  quickRfl

theorem o1 : ordIs 315 9 (mask 9) (pidn 315 9) R1 4 = true := by quickRfl
theorem o7 : ordIs 315 9 (mask 9) (pidn 315 9) Z7 6 = true := by quickRfl

theorem cV : canonK 315 9 (mask 9) (315 * 9) V = true := by quickRfl
theorem cP2 : canonK 315 9 (mask 9) (315 * 9) P2 = true := by quickRfl
theorem cP3 : canonK 315 9 (mask 9) (315 * 9) P3 = true := by quickRfl
theorem cP4 : canonK 315 9 (mask 9) (315 * 9) P4 = true := by quickRfl

theorem sV : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) PJ2.LR PJ2.TRI PJ2.BP 3 0 V = true := by
  quickRfl

theorem oV : ordIs 315 9 (mask 9) (pidn 315 9) V 4 = true := by quickRfl

theorem comm0 : Nat.beq (pcomp 315 9 (mask 9) R1 V) (pcomp 315 9 (mask 9) V R1) = true := by
  quickRfl

theorem comm : pcomp 315 9 (mask 9) R1 V = pcomp 315 9 (mask 9) V R1 :=
  Nat.eq_of_beq_eq_true comm0

theorem vne1 : (!Nat.beq V R1) = true := by quickRfl
theorem vne2 : (!Nat.beq V P2) = true := by quickRfl
theorem vne3 : (!Nat.beq V P3) = true := by quickRfl
theorem vne4 : (!Nat.beq V P4) = true := by quickRfl

@[expose] noncomputable def btIs (X C : Nat) : Bool :=
  Nat.beq (btK 315 9 (mask 9) (315 * 9) PJ2.BP 3 PJ2.LR PJ2.TR PJ2.TRI X X) C

theorem btIs_eq {X C : Nat} (h : btIs X C = true) :
    btK 315 9 (mask 9) (315 * 9) PJ2.BP 3 PJ2.LR PJ2.TR PJ2.TRI X X = C :=
  Nat.eq_of_beq_eq_true h

theorem b1_0 : btIs R1 50 = true := by quickRfl

theorem b2_0 : btIs R2 50 = true := by quickRfl

theorem b3_0 : btIs R3 300 = true := by quickRfl

theorem b4_0 : btIs R4 300 = true := by quickRfl

theorem b7_0 : btIs Z7 7 = true := by quickRfl

end CertificateChecks.KernelSporSch.J2F67Chk

end
