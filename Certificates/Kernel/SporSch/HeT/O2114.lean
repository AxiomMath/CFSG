module

public import Certificates.Kernel.SporSch.HeT.X2114
public meta import CFSG.Sporadic.HeldB.InnerData
meta import Certificates.Kernel.SporSch.HeT.X2114
meta import Certificates.Kernel.SporSch.Mathieu.GenOddPt
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeX14

meta def O0src : Array (Array Nat) := CFSG.KS.SporSch.OddPtG.oddCodes 240 315 2048 SX0 baseX0

meta def O1src : Array (Array Nat) := CFSG.KS.SporSch.OddPtG.oddCodes 42 21 2048 SX1 baseX1

end CertificateChecks.KernelSporSch.HeX14

#kmisc_packarrs CertificateChecks.KernelSporSch.HeX14.O0 CertificateChecks.KernelSporSch.HeX14.O0src 64

#kmisc_packarrs CertificateChecks.KernelSporSch.HeX14.O1 CertificateChecks.KernelSporSch.HeX14.O1src 64

namespace CertificateChecks.KernelSporSch.HeX14

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.OddPt
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

@[expose] noncomputable def oddB0 (s : Nat) : Bool :=
  oddPK 240 8 (mask 8) (240 * 8) (pidn 240 8) X0Q.LR X0Q.TR X0Q.TRI 3 315 O0 (s * 2048) 2048

@[expose] noncomputable def oddB1 (s : Nat) : Bool :=
  oddPK 42 6 (mask 6) (42 * 6) (pidn 42 6) X1Q.LR X1Q.TR X1Q.TRI 6 21 O1 (s * 2048) 2048

end CertificateChecks.KernelSporSch.HeX14

#kss_each CertificateChecks.KernelSporSch.HeX14.O0B CertificateChecks.KernelSporSch.HeX14.oddB0 40

#kss_each CertificateChecks.KernelSporSch.HeX14.O1B CertificateChecks.KernelSporSch.HeX14.oddB1 6

namespace CertificateChecks.KernelSporSch.HeX14

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.MOC CFSG.KS.SporSch.OddPt
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem nO0 : Nat.ble (ordK X0Q.LR 3) (Nat.mul 40 2048) = true := by quickRfl

theorem nO1 : Nat.ble (ordK X1Q.LR 6) (Nat.mul 6 2048) = true := by quickRfl

theorem x0_odd : oddWitnessOK 240 315 (allTables heX0) = true :=
  chainK_oddPt (by decide) (by decide) chainX0 (Nat.le_of_ble_eq_true nO0) O0B.all

theorem x1_odd : oddWitnessOK 42 21 (allTables heX1) = true :=
  chainK_oddPt (by decide) (by decide) chainX1 (Nat.le_of_ble_eq_true nO1) O1B.all

end CertificateChecks.KernelSporSch.HeX14

end
