module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Fix.DataK
public import Certificates.Kernel.Sporadic.Fi24Orb.Data
public import Certificates.Kernel.Sporadic.Fi24G2e.Data
public import Certificates.Data.Kernel.Spor.Fi24Kn
public import Certificates.Data.Kernel.Spor.Fi24G2d
public import Certificates.Data.Kernel.Spor.Fi24Fix

#kc_repo #kc_json_gz CFSG.KD.Fi24F3d.J "Certificates/Kernel/Sporadic/Fi24F3d/data/f3d.json.gz" 7317
  17360795821460123783
  (LE : List Nat) (AE : List Nat) (BE : List Nat) (CE : List (List Nat)) (KE : List Nat)
  (LEF : List Nat) (AEF : List Nat) (BEF : List Nat) (CEF : List (List Nat)) (KEF : List Nat)
  (LY : List Nat) (AY : List Nat) (BY : List Nat) (CY : List (List Nat)) (KY : List Nat)

public section

namespace CFSG.KD.Fi24F3d

open CFSG.KC.Fi24Kn

@[expose] def WE : List Nat := [11, 10, 0, 1]

@[expose] def WF : List Nat := [3, 4, 5, 6]

@[expose] def WEF : List Nat := [11, 10, 0, 1, 3, 4, 5, 6]

@[expose] def WY : List Nat := [8, 7, 3, 4, 5, 6]

@[expose] def NS : List Nat :=
  [2, 1, 0, 10, 11, 3, 2, 1, 0, 10, 4, 3, 2, 1, 0, 5, 4, 3, 2, 1, 6, 5, 4, 3, 2, 8]

@[expose] def N2 : List Nat := [5, 4, 6, 8]

@[expose] def N3 : List Nat := [4, 6, 5, 8]

@[expose] def N4 : List Nat := [3, 5, 6, 5]

@[expose] def C0 : List Nat :=
  [0, 1, 2, 7, 3, 2, 4, 3, 5, 4, 7, 3, 10, 0, 1, 2, 3, 4, 7, 3, 8, 7, 11, 10, 0, 1, 2, 3, 4, 5, 6, 9]

@[expose] noncomputable def LE (j : Nat) : Nat := nthN J.LE j

@[expose] noncomputable def LEF (j : Nat) : Nat := nthN J.LEF j

@[expose] noncomputable def LY (j : Nat) : Nat := nthN J.LY j

end CFSG.KD.Fi24F3d

end
