module

public import Certificates.Kernel.S7TwinSp6.Data
public import Certificates.Data.Kernel.S7TwinK
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS7Sp6

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P CFSG.KC.S7TwinK
open CertificateChecks.KernelLC.Sp6J Certificates.S7TwinSp6

@[expose] noncomputable def wS (w : List Int) : Nat := wordK 36 6 (mask 6) (pidn 36 6) SQ.S SQ.SI w

@[expose] noncomputable def X0 : Nat := wS [1, 3, 2, 4, 1, 3, 4, 2]

@[expose] noncomputable def Y0 : Nat := wS [1, 2, 4, 2, 4, 3]

@[expose] noncomputable def sp0K : List Nat :=
  pspan 36 6 X0 (pinv 36 6 X0) Y0 (pinv 36 6 Y0)

@[expose] noncomputable def repsK : List Nat :=
  (List.range fourWords.length).map fun i => RS.E (lget RS.OFF i)

@[expose] noncomputable def candK (j : Nat) : Nat :=
  wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (candWords.getD j [])

@[expose] noncomputable def candsK : List (List (Nat × Nat)) :=
  perRep.map (List.map fun j => (candK j, pinv 36 6 (candK j)))

@[expose] noncomputable def badY (P : Nat) : Bool :=
  bAnd(ordIs 36 6 (mask 6) (pidn 36 6) P (4 - 1), !pairsY 36 6 sp0K repsK candsK P)

theorem kG : allN sylWords.length (fun j => bAnd(lettersK 2 (sylWords.getD j []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) XQ.S XQ.SI (sylWords.getD j [])) (SQ.S j))) =
    true := by quickRfl

theorem kP : allN 4 (fun j => permOK 36 6 (mask 6) (36 * 6) (SQ.S j) (SQ.SI j)) = true := by
  quickRfl

theorem kC : allN 4 (fun j => bAnd(canonK 36 6 (mask 6) (36 * 6) (SQ.S j),
    canonK 36 6 (mask 6) (36 * 6) (SQ.SI j))) = true := by quickRfl

theorem kN : Nat.beq (ordK SQ.LR 4) 512 = true := by quickRfl

theorem kT : Nat.beq NS.CS.sum RS.N = true := by quickRfl

theorem kW : allN fourWords.length (fun i => bAnd(lettersK 4 (fourWords.getD i []),
    Nat.beq (wordK 36 6 (mask 6) (pidn 36 6) SQ.S SQ.SI (fourWords.getD i []))
      (RS.E (lget RS.OFF i)))) = true := by quickRfl

theorem kO : allN fourWords.length (fun i => bAnd(canonK 36 6 (mask 6) (36 * 6)
    (RS.E (lget RS.OFF i)), ordIs 36 6 (mask 6) (pidn 36 6) (RS.E (lget RS.OFF i)) (4 - 1))) =
    true := by quickRfl

theorem kOff : offOK RS.CS RS.OFF RS.N = true := by quickRfl

theorem kPos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RS.CS = true := by quickRfl

theorem kR : allN RS.N (repK 36 6 SQ.S SQ.SI 4 RS.CS RS.OFF RS.CI RS.E RS.P RS.L RS.K
    RS.S RS.SI RS.N 4000) = true := by quickRfl

theorem kXL : lettersK 4 [1, 3, 2, 4, 1, 3, 4, 2] = true := by quickRfl

theorem kYL : lettersK 4 [1, 2, 4, 2, 4, 3] = true := by quickRfl

theorem kXC : canonK 36 6 (mask 6) (36 * 6) X0 = true := by quickRfl

theorem kYC : canonK 36 6 (mask 6) (36 * 6) Y0 = true := by quickRfl

theorem kK0 : pq8Rel 36 6 X0 (pinv 36 6 X0) Y0 (pinv 36 6 Y0) = true := by quickRfl

theorem kCandL : allN candWords.length (fun j => lettersK 2 (candWords.getD j [])) = true := by
  quickRfl

theorem kCandC : allN candWords.length (fun j => canonK 36 6 (mask 6) (36 * 6) (candK j)) =
    true := by quickRfl

theorem ch517201p : Nat.beq (enumFrom 36 6 (mask 6) (36 * 6) SQ.LR SQ.TR badY 4 0 One36 0) 0 =
    true := by quickRfl

end CertificateChecks.KernelS7Sp6

end
