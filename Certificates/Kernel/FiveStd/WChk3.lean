module

public import Certificates.Kernel.FiveStd.WChk
public import Certificates.Kernel.FiveStd.NxData
public import Certificates.Data.Kernel.FiveStdKW3
public import Certificates.Kernel.FiveStd.NChk

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] def WK (i : Nat) : Nat := if i = 2 then 2 else 0

@[expose] def XXc (i : Nat) : List Nat :=
  if i = 0 then
    [78876, 78901, 78926, 78951, 78976, 82001, 82026, 82051, 82076, 82101, 85126, 85151, 85176, 85201,
      85226, 88251, 88276, 88301, 88326, 88351, 91376, 91401, 91426, 91451, 91476]
  else if i = 1 then
    [78876, 78926, 78976, 78901, 78951, 82001, 82051, 82101, 82026, 82076, 85126, 85176, 85226, 85151,
      85201, 88251, 88301, 88351, 88276, 88326, 91376, 91426, 91476, 91401, 91451]
  else
    [78876, 79090, 79159, 79373, 78812, 29501, 29715, 29784, 29998, 29437, 133004, 132935, 132871,
      132657, 132593, 108377, 108655, 108313, 108591, 108249, 119128, 118995, 119342, 119064, 118781]

@[expose] noncomputable def NXc (i : Nat) : List Nat := if i = 0 then NX0 else if i = 1 then NX1 else NX2

@[expose] def WD (i : Nat) : Nat := if i = 2 then 23165 else 126915

@[expose] def WW (i : Nat) : List (Nat × Nat) :=
  if i = 0 then
    [(78901, 409405), (78926, 412540), (78951, 412570), (78976, 409440), (82001, 78795), (85126, 79410),
      (88251, 80040), (91376, 80655)]
  else if i = 1 then
    [(78926, 412540), (78976, 409440), (78901, 409405), (78951, 412570), (82001, 78795), (85126, 79410),
      (88251, 80040), (91376, 80655)]
  else
    [(79090, 412540), (79159, 409443), (79373, 409407), (78812, 412572), (29501, 29420), (133004, 24415),
      (108377, 26910), (119128, 18780)]

theorem wx_xx : ∀ i < 3, XXc i = ppK (WT.getD i (0, 0, 0, 0)).2.1 (WT.getD i (0, 0, 0, 0)).2.2.1 5 5 := by
  decide +kernel

theorem wx_nx : ∀ i < 3, NXc i = (XXc i).flatMap fun x => (HT (WK i)).flatMap fun h =>
    [oneK, (WT.getD i (0, 0, 0, 0)).1].map fun e => mulK (mulK x h) e := by
  decide +kernel

theorem wx_d : ∀ i < 3, validK (WD i) = true ∧
    Nat.beq (cjK (WD i) (invK (WD i)) (RP.getD 2 0)) (WT.getD i (0, 0, 0, 0)).2.1 = true := by
  decide +kernel

theorem wx0 : nxK 82001 78901 (WD 0) (invK (WD 0)) (CB.getD 2 0) (CM.getD 2 0) (OR.getD 2 0) (OM.getD 2 0)
    (XXc 0) (NXc 0) (WW 0) = true := by
  decide +kernel

theorem wx1 : nxK 82001 78926 (WD 1) (invK (WD 1)) (CB.getD 2 0) (CM.getD 2 0) (OR.getD 2 0) (OM.getD 2 0)
    (XXc 1) (NXc 1) (WW 1) = true := by
  decide +kernel

theorem wx2 : nxK 29501 79090 (WD 2) (invK (WD 2)) (CB.getD 2 0) (CM.getD 2 0) (OR.getD 2 0) (OM.getD 2 0)
    (XXc 2) (NXc 2) (WW 2) = true := by
  decide +kernel

theorem wxs0 : nxSup (XXc 0) (NXc 0) 82001 78901 = true := by decide +kernel

theorem wxs1 : nxSup (XXc 1) (NXc 1) 82001 78926 = true := by decide +kernel

theorem wxs2 : nxSup (XXc 2) (NXc 2) 29501 79090 = true := by decide +kernel

end CertificateChecks.FiveStd

end
