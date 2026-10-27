module

public import Certificates.Kernel.Ru4120.D
public import Certificates.Data.Kernel.Kc3E16K
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRuInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.K1.Interface
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseVec
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Th.F2Spec
public import Certificates.Certificate113

public section

#kc_select CFSG.KD.Ru4120 TF TF 486
#kc_select CFSG.KD.Ru4120 ER E 256
#kc_select CFSG.KD.Ru4120 VR V 687
#kc_select CFSG.KD.Ru4120 PR P 687
#kc_select CFSG.KD.Ru4120 CR C 687
#kc_select CFSG.KD.Ru4120 NM NM 687
#kc_select CFSG.KD.Ru4120 FM FM 687
#kc_select CFSG.KD.Ru4120 RI RI 15
#kc_listDispatch CFSG.KD.Ru4120 NB NB 687
#kc_listDispatch CFSG.KD.Ru4120 FL FL 687
#kc_listDispatch CFSG.KD.Ru4120 FR FR 15

namespace CFSG.KD.Ru4120

open CFSG.QuasithinUnique.K1.SporadicPerm (ruProg)

@[expose] def pairsOf : List Nat → List (Nat × Nat)
  | a :: b :: l => (a, b) :: pairsOf l
  | _ => []

@[expose] noncomputable def progX : List (Nat × Nat) := ruProg ++ pairsOf XP

@[expose] noncomputable def EL (k : Nat) : Nat :=
  fld(ER (Nat.shiftRight k (nat_lit 6)), Nat.mul (nat_lit 130) (Nat.land k (nat_lit 63)),
    nat_lit 1361129467683753853853498429727072845823)

@[expose] noncomputable def eu (k : Nat) : Nat := Nat.land (EL k) (nat_lit 511)
@[expose] noncomputable def ev (k : Nat) : Nat := fld(EL k, nat_lit 9, nat_lit 511)
@[expose] noncomputable def tg (c k : Nat) : Nat :=
  fld(EL k, Nat.add (nat_lit 18) (Nat.mul (nat_lit 14) c), nat_lit 16383)
@[expose] noncomputable def iv (k : Nat) : Nat := fld(EL k, nat_lit 60, nat_lit 1023)
@[expose] noncomputable def ky (k : Nat) : Nat := fld(EL k, nat_lit 70, nat_lit 1152921504606846975)

@[expose] noncomputable def vu (i : Nat) : Nat := Nat.land (VR i) (nat_lit 511)
@[expose] noncomputable def vv (i : Nat) : Nat := fld(VR i, nat_lit 9, nat_lit 511)
@[expose] noncomputable def kv (i : Nat) : Nat := fld(VR i, nat_lit 18, nat_lit 16383)
@[expose] noncomputable def rt (i : Nat) : Nat := fld(VR i, nat_lit 32, nat_lit 15)
@[expose] noncomputable def cj (i : Nat) : Nat := fld(VR i, nat_lit 36, nat_lit 16383)

@[expose] noncomputable def pr (i j : Nat) : Nat := fld(PR i, Nat.mul (nat_lit 10) j, nat_lit 1023)
@[expose] noncomputable def ct (i j : Nat) : Nat := fld(CR i, Nat.mul (nat_lit 8) j, nat_lit 255)

@[expose] def B : List Nat := [0, 1, 2, 3, 4]

@[expose] def gs : List Nat := [163, 172, 185]

end CFSG.KD.Ru4120

end
