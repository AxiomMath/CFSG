module

import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Data.Kernel.Spor.SlpMat

#kc_repo #kc_json_gz CFSG.KD.F24S "Certificates/Kernel/Sporadic/Fi24Seven/data/words.json.gz" 139129 15125484225747547249 (W7 : List (List Nat)) (E7 : List (List Nat)) (EK : List (List Nat)) (C7 : List (Nat × List Nat))
#kc_repo #kc_json_gz CFSG.KD.F24S "Certificates/Kernel/Sporadic/Fi24Seven/data/plan.json.gz" 132015 5373593695458915057 (LY : List Nat) (IN : List (List (Nat × Nat))) (ND : List (List Nat)) (OU : List (List (Nat × Nat))) (EQ : List (List (List Nat × List Nat))) (NE : List (List (List Nat × List Nat))) (PC : List Nat) (PN : List Nat)

public section

namespace CFSG.KD.F24S

open CFSG.KC.SlpM CFSG.KC.Loop

@[expose] noncomputable def nK : Nat := nat_lit 343

@[expose] noncomputable def nK1 : Nat := nat_lit 107

@[expose] noncomputable def nR : Nat := nat_lit 2007

@[expose] noncomputable def nR1 : Nat := nat_lit 825

@[expose] noncomputable def nBase : Nat := nat_lit 2174

@[expose] noncomputable def WL (l : Nat) : List (List Nat) :=
  Bool.rec (motive := fun _ => List (List Nat))
    (Bool.rec (motive := fun _ => List (List Nat)) (appL W7 EK) (appL W7 E7) (Nat.beq l (nat_lit 1)))
    W7 (Nat.beq l (nat_lit 0))

@[expose] noncomputable def lyK (k : Nat) : Nat := nthL (nat_lit 0) LY k

@[expose] noncomputable def inK (k : Nat) : List (Nat × Nat) := nthL List.nil IN k

@[expose] noncomputable def ndK (k : Nat) : List Nat := nthL List.nil ND k

@[expose] noncomputable def ouK (k : Nat) : List (Nat × Nat) := nthL List.nil OU k

@[expose] noncomputable def eqK (k : Nat) : List (List Nat × List Nat) := nthL List.nil EQ k

@[expose] noncomputable def neK (k : Nat) : List (List Nat × List Nat) := nthL List.nil NE k

@[expose] noncomputable def pcR (r : Nat) : Nat := nthL (nat_lit 0) PC r

@[expose] noncomputable def pnR (r : Nat) : Nat := nthL (nat_lit 0) PN r

end CFSG.KD.F24S

end
