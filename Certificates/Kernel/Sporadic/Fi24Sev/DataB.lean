module

import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.JsonGz
public import Certificates.Kernel.Sporadic.Fi24Kit.Data
public import Certificates.Data.Kernel.Spor.Fi24SevB

#kc_repo #kc_json_gz CFSG.KD.Fi24SevB "Certificates/Kernel/Sporadic/Fi24Sev/data/f6b.json.gz" 39553 7295900557856740414 (sl : List (Nat × List Nat × List Nat)) (cj : List (Nat × Nat × List Nat × List Nat)) (uW : List Nat) (vW : List Nat) (uvW : List Nat) (uv2W : List Nat) (u4W : List Nat) (u2W : List Nat) (u3W : List Nat)

public section

namespace CFSG.KD.Fi24SevB

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24Net CFSG.KC.Fi24Kit CFSG.KC.Fi24ThreeO
  CFSG.KC.Fi24Sev CFSG.KC.Fi24SevB CFSG.KD.Fi24Net CFSG.KD.Fi24Kit

@[expose] noncomputable def X : List Nat := findU sl (nat_lit 64)

@[expose] noncomputable def Y : List Nat := findU sl (nat_lit 66)

@[expose] noncomputable def C : List Nat := findU sl (nat_lit 67)

@[expose] noncomputable def slQ (i : Nat) : List (Nat × List Nat × List Nat) :=
  (sl.drop (Nat.mul i (nat_lit 111))).take (nat_lit 111)

@[expose] noncomputable def slc (i : Nat) : Bool := slIn NW NT sl (slQ i)

@[expose] noncomputable def cjc (i : Nat) : Bool :=
  allL (cjOK NW NT sl) ((cj.drop (Nat.mul i (nat_lit 3))).take (nat_lit 3))

@[expose] noncomputable def qEq : Bool :=
  eqOK NW NT [(pw X (nat_lit 7), []), (C, X ++ (Y ++ (pw X (nat_lit 6) ++ pw Y (nat_lit 6)))),
    (C ++ X, X ++ C), (C ++ Y, Y ++ C)]

@[expose] noncomputable def qNe : Bool := neOK NW NT [(C, [])]

@[expose] noncomputable def eEq : Bool :=
  eqOK NW NT [(pw uW (nat_lit 3), []), (pw vW (nat_lit 3), []), (uW ++ vW, vW ++ uW),
    (uvW, uW ++ vW), (uv2W, uW ++ (vW ++ vW)), (uW ++ Y, Y ++ uW), (vW ++ Y, Y ++ vW),
    (pw u4W (nat_lit 4), []), (u4W ++ Y, Y ++ u4W), (pw u2W (nat_lit 2), []), (u2W ++ C, C ++ u2W),
    (pw u3W (nat_lit 3), []), (u3W ++ C, C ++ u3W), (u2W ++ X, pw X (nat_lit 6) ++ u2W),
    (u2W ++ Y, pw Y (nat_lit 6) ++ (pw C (nat_lit 6) ++ u2W)), (u3W ++ X, pw X (nat_lit 4) ++ u3W),
    (u3W ++ Y, pw Y (nat_lit 2) ++ (pw C (nat_lit 4) ++ u3W))]

@[expose] noncomputable def eNe : Bool :=
  neOK NW NT [(uW, []), (vW, []), (vW, uW), (vW, uW ++ uW), (pw u4W (nat_lit 2), []), (u2W, []),
    (u3W, [])]

@[expose] noncomputable def fU : Bool := fixK NW NT uW (nat_lit 0)

@[expose] noncomputable def fV : Bool := fixK NW NT vW (nat_lit 0)

@[expose] noncomputable def fUV : Bool := fixK NW NT uvW (nat_lit 3240)

@[expose] noncomputable def fUV2 : Bool := fixK NW NT uv2W (nat_lit 3240)

@[expose] noncomputable def fU3 : Bool := fixK NW NT u3W (nat_lit 378)

@[expose] noncomputable def fY : Bool := fixK NW NT Y (nat_lit 21)

@[expose] noncomputable def fC : Bool := fixK NW NT C (nat_lit 0)

end CFSG.KD.Fi24SevB

end
