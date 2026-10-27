
module

public import Certificates.Data.Kernel.MonsterB.IndOrb
public import Certificates.Kernel.MonsterB.IndOrbData
public import CFSG.Monster.B.Fischer.InducedOrbitChecksInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMonB.IndOrbChecks

open CFSG.KC.IndOrb CFSG.KC.U6Orb CFSG.KLie.CT CFSG.Monster.B.Fischer CertificateChecks.KernelMonB

set_option maxRecDepth 100000

@[expose] def sW : List (List Nat) :=
  [[1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1,
      1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0,
      1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
      0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
      0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]]

@[expose] def s2W : List (List Nat) :=
  [[0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1,
      1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
      1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1]]

noncomputable abbrev zA (g x : Nat) : Nat := zActK (IG.F 0) (IG.F 1) 1046 g x

theorem kWInv : invTabOK (IW 0) 12 (IW 1) 12 1024 = true := by quickRfl

theorem kW0 : orbOK linW 2 (IW 0) 12 0 1 (IW 2) 12 0 = true := by quickRfl

theorem kW1 : orbOK linW 2 (IW 0) 12 1 22 (IW 3) 12 1 = true := by quickRfl

theorem kW3 : orbOK linW 2 (IW 0) 12 23 231 (IW 4) 12 3 = true := by quickRfl

theorem kW7 : orbOK linW 2 (IW 0) 12 254 770 (IW 5) 12 7 = true := by quickRfl

theorem kZInv : invTabOK (IZ 0) 12 (IZ 1) 12 2464 = true := by quickRfl

theorem kZ0 : orbOK zA 2 (IZ 0) 12 0 462 (IZ 2) 12 0 = true := by quickRfl

theorem kZ24 : orbOK zA 2 (IZ 0) 12 462 770 (IZ 3) 12 24 = true := by quickRfl

theorem kZ1 : orbOK zA 2 (IZ 0) 12 1232 1232 (IZ 4) 12 1 = true := by quickRfl

theorem kRange0 : rangeOK (IG.F 0) 3510 2464 1046 1046 = true := by quickRfl

theorem kRange1 : rangeOK (IG.F 1) 3510 2464 1046 1046 = true := by quickRfl

theorem kFix : fixAt (IG.F 0) (IG.F 1) sW 29 = true := by quickRfl

theorem kFix2 : fixAt (IG.F 0) (IG.F 1) s2W 1047 = true := by quickRfl

theorem kFixW : fixOK (IG.F 0) (IG.F 1) sW [7] (IW 0) 12 254 770 22 = true := by quickRfl

theorem kFixZ : fixOK (IG.F 0) (IG.F 1) sW [24] (IZ 0) 12 462 770 1046 = true := by quickRfl

theorem kFix2Z : fixOK (IG.F 0) (IG.F 1) s2W [1, 277] (IZ 0) 12 1232 1232 1046 = true := by
  quickRfl

theorem kSigK : keyOK (ISg.F 0) 770 (IW 6) (IW 1) 12 1024 254 770 = true := by quickRfl

theorem kTauK : keyOK (ITa.F 0) 1232 (IZ 6) (IZ 1) 12 2464 1232 1232 = true := by quickRfl

theorem kSig : sigOK (IG.F 0) (IG.F 1) 1046 (IW 0) 254 770 (IW 5) (IW 6) (IZ 5) (IZ 1) 2464 462 770 =
    true := by quickRfl

theorem kTau : tauOK (IG.F 0) (IG.F 1) 1046 (IZ 0) 1232 1232 (IZ 6) (IZ 1) 2464 = true := by
  quickRfl

theorem kPts : (Nat.beq (fget (IW 6) 7 12) 24 && Nat.beq (fget (IZ 6) 1 12) 277) = true := by
  quickRfl

end CertificateChecks.KernelMonB.IndOrbChecks

end
