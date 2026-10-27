module

public import Certificates.Kernel.LocalComp.Sp6Root.Data
public import Certificates.Kernel.LocalComp.Sp6J.ClsX
public import Certificates.Data.Kernel.Sp6Root
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.SporSch.MathieuBT
public import Certificates.Data.Kernel.Spor.MCount
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Sp6Root

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.Sp6Root CertificateChecks.KernelLC.Sp6J

@[expose] noncomputable def P1K : Nat :=
  wordK 36 6 (mask 6) (pidn 36 6) C2Q.S C2Q.SI [1, 1, 1, 1]

@[expose] noncomputable def P2K : Nat :=
  wordK 36 6 (mask 6) (pidn 36 6) C2Q.S C2Q.SI [1, 1, 2, 1, 1, 2]

@[expose] noncomputable def sylSpec (P Q : Nat) : List Nat :=
  [pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 0) (powK 36 6 (mask 6) (pidn 36 6) Q 0),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 0) (powK 36 6 (mask 6) (pidn 36 6) Q 1),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 0) (powK 36 6 (mask 6) (pidn 36 6) Q 2),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 1) (powK 36 6 (mask 6) (pidn 36 6) Q 0),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 1) (powK 36 6 (mask 6) (pidn 36 6) Q 1),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 1) (powK 36 6 (mask 6) (pidn 36 6) Q 2),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 2) (powK 36 6 (mask 6) (pidn 36 6) Q 0),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 2) (powK 36 6 (mask 6) (pidn 36 6) Q 1),
   pcomp 36 6 (mask 6) (powK 36 6 (mask 6) (pidn 36 6) P 2) (powK 36 6 (mask 6) (pidn 36 6) Q 2)]

@[expose] noncomputable def W3K : Nat := wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI [2, 2]

@[expose] noncomputable def W3IK : Nat := wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI [-2, -2]

@[expose] noncomputable def W4K : Nat := wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI [2, 2, 2]

@[expose] noncomputable def W4IK : Nat := wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI [-2, -2, -2]

theorem ch1027001L : bAnd(lettersK 3 [1, 1, 1, 1], lettersK 3 [1, 1, 2, 1, 1, 2]) = true := by
  quickRfl

theorem ch1027001p1 : bAnd(canonK 36 6 (mask 6) (36 * 6) P1K,
    ordIs 36 6 (mask 6) (pidn 36 6) P1K (3 - 1)) = true := by quickRfl

theorem ch1027001p2 : bAnd(canonK 36 6 (mask 6) (36 * 6) P2K,
    ordIs 36 6 (mask 6) (pidn 36 6) P2K (3 - 1)) = true := by quickRfl

theorem ch1027001c : commK 36 6 (mask 6) (36 * 6) P1K P2K = true := by quickRfl

theorem ch1027001syl : (SylQ == sylSpec P1K P2K) = true := by quickRfl

theorem ch1027001k1 : Nat.ble (enumFrom 36 6 (mask 6) (36 * 6) C2Q.LR C2Q.TR
    (k1P 36 6 (mask 6) (pidn 36 6) SylQ) 4 0 One36 0) 7 = true := by quickRfl

theorem ch1027001cls : clsOneR 36 6 tA tB 2 4000 D1 = true := by quickRfl

theorem ch1027001ne : Nat.blt 0 (CFSG.KS.Mathieu.lenN S1) = true := by quickRfl

theorem ch1027001r1 : Nat.beq D1.2.2.1 (RX.E (lget RX.OFF 0)) = true := by quickRfl

theorem ch1027001pairs : pairsK 36 6 (mask 6) (pidn 36 6) S1 S1 = true := by quickRfl

theorem ch1027001w : bAnd(bAnd(lettersK 2 [2, 2], lettersK 2 [2, 2, 2]), bAnd(permOK 36 6 (mask 6) (36 * 6) W3K W3IK,
    permOK 36 6 (mask 6) (36 * 6) W4K W4IK)) = true := by quickRfl

theorem ch1027001o3 : ordIs 36 6 (mask 6) (pidn 36 6) (pcomp 36 6 (mask 6) (RX.E (lget RX.OFF 2))
    (pcomp 36 6 (mask 6) (pcomp 36 6 (mask 6) W3K (RX.E (lget RX.OFF 2))) W3IK)) (5 - 1) = true := by
  quickRfl

theorem ch1027001o4 : ordIs 36 6 (mask 6) (pidn 36 6) (pcomp 36 6 (mask 6) (RX.E (lget RX.OFF 3))
    (pcomp 36 6 (mask 6) (pcomp 36 6 (mask 6) W4K (RX.E (lget RX.OFF 3))) W4IK)) (6 - 1) = true := by
  quickRfl

end CertificateChecks.KernelLC.Sp6Root

end
