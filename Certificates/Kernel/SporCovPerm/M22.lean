module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.SporCov.Defs
public import Certificates.Data.Kernel.SporCov.PCl
public import Certificates.Data.Kernel.SporCov.BaseKit
public import Certificates.Data.Kernel.SporCov.Census

#kc_repo #kc_json_gz CFSG.KD.SporCovPerm.M22.F "Certificates/Kernel/SporCovPerm/data/m22.json.gz" 3570
  8202082781155986840
  (G1 : List Nat) (G2 : List Nat) (T : List Nat) (M : List (List Nat)) (Y : List (List Nat))
  (H : List (List Nat)) (Yc : List (List Nat)) (K : List Nat) (C : List (List Nat))
  (R : List (List Nat)) (A : List (List Nat))

set_option Elab.async false

public section

namespace CFSG.KD.SporCovPerm.M22

open CFSG.KC.SporCov

@[expose] noncomputable def bs : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

@[expose] noncomputable def E : List Nat → List Nat → Bool :=
  eqB (nthN (nthW F.A 0)) (nthN (nthW F.A 1)) (nthN (nthW F.A 2)) (nthN (nthW F.A 3)) bs

@[expose] noncomputable def chk (E : List Nat → List Nat → Bool) : Bool :=
  pclOK E letP 13 4 2 F.G1 F.G2 F.T F.M F.Y F.H F.Yc F.C F.R F.K && chW letP F.G1 &&
    chW letP F.G2 && cm E F.G1 F.G2 && E (repW F.G1 3) [] && E (repW F.G2 3) [] &&
    E (repW F.T 3) [] && neOK E F.T

namespace Ck

theorem ok : chk E = true := by quickRfl

end Ck

end CFSG.KD.SporCovPerm.M22

end
