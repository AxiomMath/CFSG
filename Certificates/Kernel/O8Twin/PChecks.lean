module

public import Certificates.Kernel.O8Twin.PData
public import Certificates.Data.Kernel.S7TwinK
public import Certificates.Data.Kernel.Child3
public import Certificates.Data.Kernel.J2Cover
public import Certificates.Data.Kernel.SporSch.MathieuBT
public import Certificates.Data.Kernel.AE6Core
import CFSG.Certificates.Kernel.Common.Harness
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Twin

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KC.Child3
open CFSG.KS.M11 CFSG.KS.SporSch.MBT CFSG.KC.KGC31P CFSG.KC.S7TwinK CFSG.KC.AE6Core
open Certificates.S7TwinO8

@[expose] noncomputable def GPf (j : Nat) : Nat := lget GP j

@[expose] noncomputable def wS (w : List Int) : Nat :=
  wordK 120 7 (mask 7) (pidn 120 7) ST.S ST.SI w

@[expose] noncomputable def X0 : Nat := wS [2, 1, 2, 3, 2, 4, 2, 1, 2, 3, 2, 4]

@[expose] noncomputable def Y0 : Nat := wS [1, 3, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4, 2]

@[expose] noncomputable def sp0K : List Nat :=
  pspan 120 7 X0 (pinv 120 7 X0) Y0 (pinv 120 7 Y0)

@[expose] noncomputable def repsK : List Nat :=
  (List.range fourWords.length).map fun i => RS.E (lget RS.OFF i)

@[expose] noncomputable def candL : List (List Int) := wordsL CW.chars

@[expose] noncomputable def candK (j : Nat) : Nat :=
  wordK 120 7 (mask 7) (pidn 120 7) GPf GPf (candL.getD j [])

@[expose] noncomputable def candsK : List (List (Nat × Nat)) :=
  perRep.map (List.map fun j => (candK j, pinv 120 7 (candK j)))

@[expose] noncomputable def badY (P : Nat) : Bool :=
  bAnd(ordIs 120 7 (mask 7) (pidn 120 7) P (4 - 1), !pairsY 120 7 sp0K repsK candsK P)

theorem kGP : Nat.beq GP.length 8 = true := by decide +kernel

theorem kGPp : allN 8 (fun j => bAnd(permOK 120 7 (mask 7) (120 * 7) (GPf j) (GPf j),
    canonK 120 7 (mask 7) (120 * 7) (GPf j))) = true := by
  decide +kernel

theorem kG : allN 4 (fun j => Nat.beq (GPf (2 * j)) (ST.S j)) = true := by decide +kernel

theorem kSI : allN 4 (fun j => Nat.beq (ST.SI j) (ST.S j)) = true := by decide +kernel

theorem kT : Nat.beq NS.CS.sum RS.N = true := by decide +kernel

theorem kW : allN fourWords.length (fun i => bAnd(lettersK 4 (fourWords.getD i []),
    Nat.beq (wordK 120 7 (mask 7) (pidn 120 7) ST.S ST.SI (fourWords.getD i []))
      (RS.E (lget RS.OFF i)))) = true := by
  decide +kernel

theorem kO : allN fourWords.length (fun i => bAnd(canonK 120 7 (mask 7) (120 * 7)
    (RS.E (lget RS.OFF i)), ordIs 120 7 (mask 7) (pidn 120 7) (RS.E (lget RS.OFF i)) (4 - 1))) =
    true := by
  decide +kernel

theorem kOff : offOK RS.CS RS.OFF RS.N = true := by decide +kernel

theorem kPos : CFSG.KC.J2Cover.allL (fun c => Nat.blt 0 c) RS.CS = true := by decide +kernel

theorem kR : allN RS.N (repK 120 7 ST.S ST.SI 4 RS.CS RS.OFF RS.CI RS.E RS.P RS.L RS.K
    RS.S RS.SI RS.N 4000) = true := by
  decide +kernel

theorem kXL : lettersK 4 [2, 1, 2, 3, 2, 4, 2, 1, 2, 3, 2, 4] = true := by decide +kernel

theorem kYL : lettersK 4 [1, 3, 2, 1, 2, 4, 2, 1, 3, 2, 1, 4, 2] = true := by decide +kernel

theorem kXC : canonK 120 7 (mask 7) (120 * 7) X0 = true := by decide +kernel

theorem kYC : canonK 120 7 (mask 7) (120 * 7) Y0 = true := by decide +kernel

theorem kK0 : pq8Rel 120 7 X0 (pinv 120 7 X0) Y0 (pinv 120 7 Y0) = true := by decide +kernel

theorem kToks : toksOKw CW.chars = true := by decide +kernel

theorem kCandN : Nat.beq candL.length 12 = true := by decide +kernel

theorem kCandL : allN candL.length (fun j => lettersK 8 (candL.getD j [])) = true := by
  decide +kernel

theorem kCandC : allN candL.length (fun j => canonK 120 7 (mask 7) (120 * 7) (candK j)) =
    true := by
  decide +kernel

end CertificateChecks.KernelO8Twin

end
