module

public import Certificates.Data.Kernel.Sp43KCase
public import Certificates.Kernel.Sp43K.Sel2
public import Certificates.Kernel.Sp43K.Data3

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K

abbrev CaseT := Nat × Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat) × Nat × Nat × Nat

@[expose] noncomputable def cs : Nat → List CaseT
  | 0 => c0 | 1 => c1 | 2 => c2 | 3 => c3 | 4 => c4 | _ => []

@[expose] noncomputable def hA (j : Nat) : Nat := if j < 5 then gA j else G5.1

@[expose] noncomputable def hB (j : Nat) : Nat := if j < 5 then gB j else G5.2.1

@[expose] noncomputable def caseOne (i : Nat) (c : CaseT) : Bool :=
  let j := c.2.1
  caseK (gA i) (gB i) j (mP j) (ords.getD j 0) (hA j) (hB j) c.1 c.2.2.1 c.2.2.2.1
    c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2

@[expose] noncomputable def casesOK (i : Nat) (L : List CaseT) : Bool :=
  List.rec true (fun c _ ih => caseOne i c && ih) L

@[expose] def ncs : List Nat := [330, 67, 60, 14, 11]

@[expose] def cjobs : List (Nat × Nat) :=
  (List.range 42).map (fun k => (0, 8 * k)) ++ (List.range 9).map (fun k => (1, 8 * k)) ++
    (List.range 8).map (fun k => (2, 8 * k)) ++ [(3, 0), (3, 8), (4, 0), (4, 8)]

@[expose] noncomputable def caseC (j : Nat) : Bool :=
  let p := cjobs.getD j (0, 0)
  casesOK p.1 (((cs p.1).drop p.2).take 8)

@[expose] noncomputable def ncsC (i : Nat) : Bool :=
  (cs i).length == ncs.getD i 0 && nr.getD i 0 == ncs.getD i 0 &&
    (List.range (ncs.getD i 0)).all (fun r => fldT (xP i) r == ((cs i).getD r default).1)

end CFSG.KD.Sp43K

end
