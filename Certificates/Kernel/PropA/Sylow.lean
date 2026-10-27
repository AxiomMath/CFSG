module

public import Certificates.Kernel.PropA.Data
public import Certificates.Kernel.PropA.Words
public import Certificates.Data.Kernel.Spor.PRec
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.PRec

theorem pa450010_SD_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 64 pa450010SD.k
    pa450010SD.G pa450010SD.GI pa450010SD.cnt pa450010SD.T pa450010SD.PL 2 pa450010S1
    pa450010S1I pa450010wSD = true := by quickRfl
theorem pa450010_SD_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010SD.G pa450010SD.GI
    pa450010SD.k pa450010SD.cnt pa450010SD.T pa450010SD.PL pa450010SD.POS pa450010SD.SRT
    pa450010SD.SRI 0 64 = true := by quickRfl

theorem pa450010_SY1_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 256
    pa450010SY1.k pa450010SY1.G pa450010SY1.GI pa450010SY1.cnt pa450010SY1.T pa450010SY1.PL 4
    pa450010S1 pa450010S1I pa450010wS1 = true := by quickRfl
theorem pa450010_SY1_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010SY1.G pa450010SY1.GI
    pa450010SY1.k pa450010SY1.cnt pa450010SY1.T pa450010SY1.PL pa450010SY1.POS pa450010SY1.SRT
    pa450010SY1.SRI 0 256 = true := by quickRfl

theorem pa450010_SY2_hd : recHdK 28 5 (mask 5) (28 * 5) (pidn 28 5) (pidn 28 5) 256
    pa450010SY2.k pa450010SY2.G pa450010SY2.GI pa450010SY2.cnt pa450010SY2.T pa450010SY2.PL 4
    pa450010S2 pa450010S2I pa450010wS2 = true := by quickRfl
theorem pa450010_SY2_sl : penumSlK 28 5 (mask 5) (28 * 5) false pa450010SY2.G pa450010SY2.GI
    pa450010SY2.k pa450010SY2.cnt pa450010SY2.T pa450010SY2.PL pa450010SY2.POS pa450010SY2.SRT
    pa450010SY2.SRI 0 256 = true := by quickRfl

@[expose] noncomputable def pa450010L1 : List (Nat × (Nat → Nat) × (Nat → Nat)) :=
  [(pa450010C10.cnt, pa450010C10.T, pa450010F10), (pa450010C11.cnt, pa450010C11.T, pa450010F11),
   (pa450010C12.cnt, pa450010C12.T, pa450010F12), (pa450010C13.cnt, pa450010C13.T, pa450010F13),
   (pa450010C14.cnt, pa450010C14.T, pa450010F14), (pa450010C15.cnt, pa450010C15.T, pa450010F15)]

@[expose] noncomputable def pa450010L2 : List (Nat × (Nat → Nat) × (Nat → Nat)) :=
  [(pa450010C20.cnt, pa450010C20.T, pa450010F20), (pa450010C21.cnt, pa450010C21.T, pa450010F21),
   (pa450010C22.cnt, pa450010C22.T, pa450010F22), (pa450010C23.cnt, pa450010C23.T, pa450010F23),
   (pa450010C24.cnt, pa450010C24.T, pa450010F24), (pa450010C25.cnt, pa450010C25.T, pa450010F25)]

@[expose] noncomputable def pa450010LD : List (Nat × (Nat → Nat) × (Nat → Nat)) :=
  [(pa450010XD.cnt, pa450010XD.T, pa450010FD0), (pa450010AD.cnt, pa450010AD.T, pa450010FD1)]

theorem pa450010_cover1 : sqCoverK 28 5 (mask 5) (pidn 28 5) (pa450010S1 3) pa450010SY1.T
    pa450010L1 pa450010SY1.cnt = true := by quickRfl

theorem pa450010_cover2 : sqCoverK 28 5 (mask 5) (pidn 28 5) (pa450010S2 3) pa450010SY2.T
    pa450010L2 pa450010SY2.cnt = true := by quickRfl

theorem pa450010_coverD : sqCoverK 28 5 (mask 5) (pidn 28 5) (pidn 28 5) pa450010SD.T
    pa450010LD pa450010SD.cnt = true := by quickRfl

end CertificateChecks.KernelPropA

end
