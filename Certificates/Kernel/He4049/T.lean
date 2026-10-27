module

public import Certificates.Kernel.He4049.D
public import Certificates.Data.Kernel.Kc3E16K
import CFSG.Certificates.Kernel.Common.Harness

public section

#kc_select CFSG.KD.He4049 TF TF 343
#kc_select CFSG.KD.He4049 ER E 16
#kc_select CFSG.KD.He4049 VR V 191
#kc_select CFSG.KD.He4049 PR P 191
#kc_select CFSG.KD.He4049 CR C 191
#kc_select CFSG.KD.He4049 NM NM 191
#kc_select CFSG.KD.He4049 FM FM 191
#kc_select CFSG.KD.He4049 RI RI 25
#kc_listDispatch CFSG.KD.He4049 NB NB 191
#kc_listDispatch CFSG.KD.He4049 FL FL 191
#kc_listDispatch CFSG.KD.He4049 FR FR 25

namespace CFSG.KD.He4049

@[expose] def pairsOf : List Nat → List (Nat × Nat)
  | a :: b :: l => (a, b) :: pairsOf l
  | _ => []

@[expose] noncomputable def progX : List (Nat × Nat) := pairsOf XP

@[expose] noncomputable def EL (k : Nat) : Nat :=
  fld(ER (Nat.shiftRight k (nat_lit 6)), Nat.mul (nat_lit 136) (Nat.land k (nat_lit 63)),
    nat_lit 87112285931760246646623899502532662132735)

@[expose] noncomputable def eu (k : Nat) : Nat := Nat.land (EL k) (nat_lit 511)
@[expose] noncomputable def ev (k : Nat) : Nat := fld(EL k, nat_lit 9, nat_lit 511)
@[expose] noncomputable def tg (c k : Nat) : Nat :=
  fld(EL k, Nat.add (nat_lit 18) (Nat.mul (nat_lit 10) c), nat_lit 1023)
@[expose] noncomputable def iv (k : Nat) : Nat := fld(EL k, nat_lit 58, nat_lit 255)
@[expose] noncomputable def ky (k : Nat) : Nat := fld(EL k, nat_lit 66, nat_lit 1180591620717411303423)

@[expose] noncomputable def vu (i : Nat) : Nat := Nat.land (VR i) (nat_lit 511)
@[expose] noncomputable def vv (i : Nat) : Nat := fld(VR i, nat_lit 9, nat_lit 511)
@[expose] noncomputable def kv (i : Nat) : Nat := fld(VR i, nat_lit 18, nat_lit 1023)
@[expose] noncomputable def rt (i : Nat) : Nat := fld(VR i, nat_lit 28, nat_lit 31)
@[expose] noncomputable def cj (i : Nat) : Nat := fld(VR i, nat_lit 33, nat_lit 1023)

@[expose] noncomputable def pr (i j : Nat) : Nat := fld(PR i, Nat.mul (nat_lit 8) j, nat_lit 255)
@[expose] noncomputable def ct (i j : Nat) : Nat := fld(CR i, Nat.mul (nat_lit 7) j, nat_lit 127)

@[expose] def B : List Nat := [0, 1, 3, 4, 2]

@[expose] def gs : List Nat := [197, 207, 226, 247]

@[expose] noncomputable def TA : Array Nat :=
  ((List.range 8330).map (CFSG.KC.Enum.pg 14 16383 (TF 0))).toArray

@[expose] noncomputable def TB : Array Nat :=
  ((List.range 8330).map (CFSG.KC.Enum.pg 14 16383 (TF 1))).toArray

end CFSG.KD.He4049

end
