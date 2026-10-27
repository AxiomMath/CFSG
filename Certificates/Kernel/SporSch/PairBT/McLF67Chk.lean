module

public import Certificates.Kernel.SporSch.PairBT.McLF67Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLF67Chk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.McLBT

theorem c7 : canonK 275 9 (mask 9) (275 * 9) Z7 = true := by quickRfl

theorem c15 : canonK 275 9 (mask 9) (275 * 9) X15 = true := by quickRfl

theorem s7 :
    siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0 Z7 = true := by
  quickRfl

theorem s15 :
    siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0 X15 = true := by
  quickRfl

theorem o7 : ordIs 275 9 (mask 9) (pidn 275 9) Z7 6 = true := by quickRfl

theorem o15 : ordIs 275 9 (mask 9) (pidn 275 9) X15 14 = true := by quickRfl

@[expose] noncomputable def btIs (X C : Nat) : Bool :=
  Nat.beq (btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI X X) C

theorem btIs_eq {X C : Nat} (h : btIs X C = true) :
    btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI X X = C :=
  Nat.eq_of_beq_eq_true h

theorem b7_0 : btIs Z7 14 = true := by quickRfl

theorem b15_0 : btIs X15 30 = true := by quickRfl

theorem b7 : btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI Z7 Z7 = 14 :=
  btIs_eq b7_0

theorem b15 : btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI X15 X15 = 30 :=
  btIs_eq b15_0

end CertificateChecks.KernelSporSch.McLF67Chk

end
