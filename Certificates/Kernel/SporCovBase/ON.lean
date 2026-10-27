module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.Census
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.Spor.ONK
public import Certificates.Kernel.Sporadic.ON2.Data

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.ON.F3 "Certificates/Kernel/SporCovBase/data/on3.json.gz" 9707
  561630405550524435
  (S : List (List Nat)) (Q : List (List Nat)) (T : List Nat) (P : List Nat) (Tg : List (List Nat))
  (Gs : List (List Nat)) (X0 : Nat) (G1 : List Nat) (G2 : List Nat) (M : List (List Nat))
  (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat)) (K : List Nat)
  (C : List (List Nat)) (R : List (List Nat))

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.ON.F7 "Certificates/Kernel/SporCovBase/data/on7.json.gz" 3385
  7631241990651689215
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (GZ : List Nat)

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.ON

open CFSG.KC.SporCov CFSG.KS.ON CertificateChecks.KernelSpor

@[expose] noncomputable def bs : List Nat := [0, 2, 4]

@[expose] noncomputable def E : List Nat → List Nat → Bool :=
  eqB (tab ONW.A) (tab ONW.U0) (tab ONW.B) (tab ONW.U1) bs

@[expose] noncomputable def Kf (u : List Nat) : Nat :=
  imB (tab ONW.A) (tab ONW.U0) (tab ONW.B) (tab ONW.U1) u F3.X0

@[expose] noncomputable def pc3 (E : List Nat → List Nat → Bool) : Bool :=
  allLt 4 fun i => allLt 4 fun j => Nat.blt j i || pcR E 3 F3.S F3.Q 4 i j

@[expose] noncomputable def chk3 (E : List Nat → List Nat → Bool) (K : List Nat → Nat) : Bool :=
  pc3 E && cenH E letP F3.S [F3.T] F3.Gs F3.P (3 ^ 4) && keyInc K F3.S 4 3 F3.P &&
    allLt (3 ^ 4) (cenOK E 3 F3.S 4 [F3.T] F3.Gs F3.P F3.Tg (3 ^ 4)) &&
    pclOK E letP 8 2 2 F3.G1 F3.G2 F3.T F3.M F3.Y F3.H F3.Yc F3.C F3.R F3.K && chW letP F3.G1 &&
    chW letP F3.G2 && cm E F3.G1 F3.G2 && E (repW F3.G1 3) [] && E (repW F3.G2 3) []

@[expose] noncomputable def chk7 (E : List Nat → List Nat → Bool) : Bool :=
  p3cOK E letP 7 F7.E1 F7.E2 4 2 2 F7.G1 F7.G2 F7.Z F7.T F7.GZ F7.M F7.Y F7.H F7.Yc F7.C F7.R F7.K

namespace Ck

theorem ok3 : chk3 E Kf = true := by quickRfl

theorem ok7 : chk7 E = true := by quickRfl

end Ck

end CFSG.KD.SporCovBase.ON

end
