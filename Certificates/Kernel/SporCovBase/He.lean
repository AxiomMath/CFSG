module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.Spor.PEnum
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Kernel.HeTab.Data

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.He.F3 "Certificates/Kernel/SporCovBase/data/he3.json.gz" 2608
  12794876632364487936
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (GZ : List Nat)

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.He.F5 "Certificates/Kernel/SporCovBase/data/he5.json.gz" 4150
  1226357633754216699
  (G1 : List Nat) (G2 : List Nat) (T : List Nat) (M : List (List Nat)) (Y : List (List Nat))
  (H : List (List Nat)) (Yc : List (List Nat)) (K : List Nat) (C : List (List Nat))
  (R : List (List Nat))

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.He.F7 "Certificates/Kernel/SporCovBase/data/he7.json.gz" 3305
  6819540877619384230
  (G1 : List Nat) (G2 : List Nat) (Z : List Nat) (E1 : Nat) (E2 : Nat) (T : List Nat)
  (M : List (List Nat)) (Y : List (List Nat)) (H : List (List Nat)) (Yc : List (List Nat))
  (K : List Nat) (C : List (List Nat)) (R : List (List Nat)) (GZ : List Nat)

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.He

open CFSG.KC.SporCov CFSG.KS.PEnum

@[expose] noncomputable def bs : List Nat := [0, 1, 3, 4, 2]

@[expose] noncomputable def E : List Nat → List Nat → Bool :=
  eqB (r32 CFSG.KD.HeOrb.AL) (r32 CFSG.KD.HeOrb.AL) (r32 CFSG.KD.HeOrb.BE) (r32 CFSG.KD.HeTab.BI) bs

@[expose] noncomputable def chk3 (E : List Nat → List Nat → Bool) : Bool :=
  p3cOK E letP 3 F3.E1 F3.E2 3 1 2 F3.G1 F3.G2 F3.Z F3.T F3.GZ F3.M F3.Y F3.H F3.Yc F3.C F3.R F3.K

@[expose] noncomputable def chk5 (E : List Nat → List Nat → Bool) : Bool :=
  pclOK E letP 5 3 2 F5.G1 F5.G2 F5.T F5.M F5.Y F5.H F5.Yc F5.C F5.R F5.K && chW letP F5.G1 &&
    chW letP F5.G2 && cm E F5.G1 F5.G2 && E (repW F5.G1 5) [] && E (repW F5.G2 5) [] &&
    E (repW F5.T 5) [] && neOK E F5.T

@[expose] noncomputable def chk7 (E : List Nat → List Nat → Bool) : Bool :=
  p3cOK E letP 7 F7.E1 F7.E2 3 1 2 F7.G1 F7.G2 F7.Z F7.T F7.GZ F7.M F7.Y F7.H F7.Yc F7.C F7.R F7.K

namespace Ck

theorem ok3 : chk3 E = true := by quickRfl

theorem ok5 : chk5 E = true := by quickRfl

theorem ok7 : chk7 E = true := by quickRfl

end Ck

end CFSG.KD.SporCovBase.He

end
