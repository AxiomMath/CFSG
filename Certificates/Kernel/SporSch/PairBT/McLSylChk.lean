module

public import Certificates.Kernel.SporSch.PairBT.McLSylData
public import CFSG.Certificates.Kernel.SporSch.McLSylowSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLSylChk

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CertificateChecks.KernelSporSch

@[expose] noncomputable def Z : Nat := McLSyl.XL.getD 0 0

@[expose] noncomputable def Zi : Nat := McLSyl.XL.getD 1 0

@[expose] noncomputable def G : Nat := McLSyl.XL.getD 2 0

@[expose] noncomputable def Gi : Nat := McLSyl.XL.getD 3 0

theorem sz : szOK 275 9 = true := by quickRfl

theorem cA : canonK 275 9 (mask 9) (275 * 9) (PMcL.S 0) = true := by quickRfl

theorem oA : ordIs 275 9 (mask 9) (pidn 275 9) (PMcL.S 0) 1 = true := by quickRfl

theorem cZ : canonK 275 9 (mask 9) (275 * 9) Z = true := by quickRfl

theorem cZi : canonK 275 9 (mask 9) (275 * 9) Zi = true := by quickRfl

theorem cG : canonK 275 9 (mask 9) (275 * 9) G = true := by quickRfl

theorem pZ : permOK 275 9 (mask 9) (275 * 9) Z Zi = true := by quickRfl

theorem pG : permOK 275 9 (mask 9) (275 * 9) G Gi = true := by quickRfl

theorem sZ : siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0 Z = true := by
  quickRfl

theorem sG : siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0 G = true := by
  quickRfl

theorem oZ : ordIs 275 9 (mask 9) (pidn 275 9) Z 10 = true := by quickRfl

theorem rel0 : Nat.beq (pcomp 275 9 (mask 9) G Z) (pcomp 275 9 (mask 9) Z (pcomp 275 9 (mask 9) Z
    (pcomp 275 9 (mask 9) Z G))) = true := by quickRfl

theorem rel : pcomp 275 9 (mask 9) G Z = pcomp 275 9 (mask 9) Z (pcomp 275 9 (mask 9) Z
    (pcomp 275 9 (mask 9) Z G)) := Nat.eq_of_beq_eq_true rel0

theorem bZZ0 : Nat.beq (btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI Z Z) 11 =
    true := by quickRfl

theorem bZZ : btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI Z Z = 11 :=
  Nat.eq_of_beq_eq_true bZZ0

theorem bZZi0 : Nat.beq (btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI Z Zi) 0 =
    true := by quickRfl

theorem bZZi : btK 275 9 (mask 9) (275 * 9) PMcL.BP 5 PMcL.LR PMcL.TR PMcL.TRI Z Zi = 0 :=
  Nat.eq_of_beq_eq_true bZZi0

theorem ord0 : Nat.beq (ordK PMcL.LR 5) 898128000 = true := by quickRfl

theorem ord : ordK PMcL.LR 5 = 898128000 := Nat.eq_of_beq_eq_true ord0

end CertificateChecks.KernelSporSch.McLSylChk

end
