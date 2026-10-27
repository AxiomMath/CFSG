module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Oct.Data
public import Certificates.Data.Kernel.Spor.Fi24E

#kc_repo #kc_json_gz CFSG.KD.Fi24E "Certificates/Kernel/Sporadic/Fi24E/data/e.json.gz" 776
  8032691338564015806 (p1 : Nat) (p2 : Nat) (sig1 : Nat) (tv : List Nat) (pass : List Nat)
  (pv : List Nat) (cov : Nat) (fI : List Nat) (z : Nat)

public section

namespace CFSG.KD.Fi24E

open CFSG.KC CFSG.KC.Fi24ThreeO CFSG.KC.Fi24Oct CFSG.KC.Fi24E CFSG.KD.Fi24Net CFSG.KD.Fi24Kit
  CFSG.KD.Fi24Oct

@[expose] noncomputable def c1 : List Nat := dW [nat_lit 0]

@[expose] noncomputable def c2 : List Nat := dW [nat_lit 3]

@[expose] noncomputable def cw : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [c1, c2] (fun w _ ih => dW w :: ih) wcs

@[expose] noncomputable def pp : List (Nat × Nat) := zipL pass pv

@[expose] noncomputable def fcs : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun i _ ih => prodC [wc (nat_lit 0), wc i] :: ih) fI

@[expose] noncomputable def zc : List Nat :=
  prodC [wc (nat_lit 0), wc (nat_lit 3), wc (nat_lit 13), wc (nat_lit 15)]

@[expose] noncomputable def sg : Bool := sigOK NW NT wcs p1 p2 c1 tv pp sig1

@[expose] noncomputable def cv : Bool := covW NW NT cw cov (plOf [p1]) (nat_lit 0)

@[expose] noncomputable def fx : Bool := fixAllOK NW NT fcs (plOf pts)

@[expose] noncomputable def zz : Bool := Fi24FixP.fixOK (plC NW NT) zc z

end CFSG.KD.Fi24E

end
