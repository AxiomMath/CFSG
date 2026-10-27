module

public import Certificates.Kernel.SporSch.Co1.ThreeLocal
public import CFSG.Certificates.Kernel.SporSch.Co1MatSound
public import CFSG.Certificates.Kernel.Spor.BindList
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Co1Packed

open CFSG.Sporadic.Co1Schreier.Native CFSG.KS.Raw
open CertificateChecks.KernelSporSch.Co1Rows CertificateChecks.KernelSporSch.Co1ThreeLocal

@[expose] def PA : Nat :=
  185196396100935200497972746201888525001606698601048169269830769328826080360954108538010710719741197095952176088007973760317452280257120481549676864524456224861616382882499878

@[expose] def PB : Nat :=
  189679898173089903359300468302863359754348026640600814329645816173468189026938384113965743268043737625601185997848141267265248822104807421087410016631810249835024335727824431

theorem bA : bindListK 24 24 PA RA.toList = true := by quickRfl
theorem bB : bindListK 24 24 PB RB.toList = true := by quickRfl

theorem rows_of {P : Nat} {l : List Nat} (h : bindListK 24 24 P l = true) :
    l.toArray = unpack 24 24 P := toArray_eq_of_bindListK h

theorem uA : RA = unpack 24 24 PA := by
  have h := rows_of bA
  rwa [Array.toArray_toList] at h

theorem uB : RB = unpack 24 24 PB := by
  have h := rows_of bB
  rwa [Array.toArray_toList] at h

theorem aR_u : aR = unpack 24 24 PA := aR_eq.trans uA
theorem bR_u : bR = unpack 24 24 PB := bR_eq.trans uB

end CertificateChecks.KernelSporSch.Co1Packed

end
