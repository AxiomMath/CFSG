module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.SporCov.BaseFix
public import Certificates.Data.Kernel.Fi22.Orb

#kc_repo #kc_json_gz CFSG.KD.SporCovBase.Fi22.D "Certificates/Kernel/SporCovBase/data/fi22.json.gz"
  61051 12177719431327265889
  (T : List (List Nat)) (F : List Nat) (BI : Nat) (PZ1 : List (List Nat)) (PH1 : List (List Nat))
  (PZ2 : List (List Nat)) (PH2 : List (List Nat)) (Y2c : List Nat) (G2c : List Nat)
  (Mc : List (List Nat)) (Nc : Nat) (NLc : Nat) (Cc : List (List Nat)) (Y2d : List Nat)
  (G2d : List Nat) (Md : List (List Nat)) (Nd : Nat) (NLd : Nat) (Cd : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovBase.Fi22

open CFSG.KC.SporCov CFSG.Sporadic.Fi22.Native

@[expose] noncomputable def fA (x : Nat) : Nat := orbEntry 0 x

@[expose] noncomputable def fB (x : Nat) : Nat := orbEntry 1 x

@[expose] noncomputable def fBi (x : Nat) : Nat :=
  Nat.land (Nat.shiftRight D.BI (Nat.mul 12 x)) 4095

@[expose] noncomputable def bs : List Nat := [0, 1, 6, 11, 3]

@[expose] noncomputable def E : List Nat → List Nat → Bool := eqB fA fA fB fBi bs

@[expose] noncomputable def chkT (E : List Nat → List Nat → Bool) (i : Nat) : Bool :=
  chW letP (nthW D.T i) && E (repW (nthW D.T i) 3) [] && neOK E (nthW D.T i) &&
    Nat.beq (fixB fA fA fB fBi 3510 55 (nthW D.T i)) (nthN D.F i)

@[expose] noncomputable def chkF (E : List Nat → List Nat → Bool) : Bool :=
  invB fB fBi 3510 55 && allLt 4 (chkT E)

@[expose] noncomputable def chkP (E : List Nat → List Nat → Bool) (i : Nat) : Bool :=
  genOK E letP [0] [1] [2] [3] &&
    ctlA E letP 3 (nthW D.T i) [] (nthW D.T i) (nthW D.PZ1 i) (nthW D.PH1 i) (nthW D.PZ2 i)
      (nthW D.PH2 i) [0] [1] [2] [3]

@[expose] noncomputable def chkC (E : List Nat → List Nat → Bool) (t y₂ g₂ : List Nat)
    (M C : List (List Nat)) (n nL : Nat) : Bool :=
  clH E letP 3 t t y₂ [] g₂ M nL && allLt nL (clL E t y₂ n M) && stH letP [[0], [2]] 2 &&
    allLt 2 (stOK E M C [[0], [2]])

namespace Ck

theorem okF : chkF E = true := by quickRfl

theorem okP : allLt 2 (chkP E) = true := by quickRfl

theorem okC : chkC E (nthW D.T 2) D.Y2c D.G2c D.Mc D.Cc D.Nc D.NLc = true := by quickRfl

theorem okD : chkC E (nthW D.T 3) D.Y2d D.G2d D.Md D.Cd D.Nd D.NLd = true := by quickRfl

end Ck

end CFSG.KD.SporCovBase.Fi22

end
