module

public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.Pt2085Data
public import Certificates.Data.Kernel.SporSch.HNXPath
public import CFSG.Certificates.Kernel.Local.HN.X.Data
import CFSG.Certificates.Kernel.Common.Harness

public noncomputable section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2085

open CFSG.KC.LL.HNX CFSG.KD.HNPt2085 CFSG.KD.LgHNX CFSG.KC.LL

local notation "R" => CFSG.KD.HNPt.R
local notation "mm" => CFSG.KC.LL.HN.mm

@[expose] noncomputable def om (t : Nat) : Nat := fldW OM (Nat.mul 21 t) 21

@[expose] noncomputable def TIL: List Nat := [TI0, TI1, TI2, TI3, TI4, TI5]

@[expose] noncomputable def ESL: List Nat := [ES0, ES1, ES2, ES3, ES4, ES5]

@[expose] noncomputable def EDL: List Nat := [ED0, ED1, ED2, ED3, ED4, ED5]

@[expose] noncomputable def src (l e : Nat) : Nat := fldW (lget ESL l) (Nat.mul 21 e) 21

@[expose] noncomputable def dst (l e : Nat) : Nat := fldW (lget EDL l) (Nat.mul 21 e) 21

@[expose] noncomputable def omImg (G : Nat) (J : List Nat) : Bool :=
  ptsFn TX MS CM3 M G om (fun t => om (lget J t)) 50

@[expose] noncomputable def idsAt (c : Nat) : Bool :=
  idsOk src dst TW IS (lget CH c) IDS (lgetL ST c)

theorem w_F : wordC R fc = F ∧ wordC R g5c = G5 := by decide +kernel
theorem w_I : wordC R ic0 = I0 ∧ wordC R ic1 = I1 ∧ wordC R ic2 = I2 ∧ wordC R ic3 = I3 ∧
    wordC R ic4 = I4 ∧ wordC R ic5 = I5 := by decide +kernel
theorem w_E : wordC R ec0 = E0 ∧ wordC R ec1 = E1 ∧ wordC R ec2 = E2 ∧ wordC R ec3 = E3 := by
  decide +kernel

theorem t_F : trM F = TF ∧ trM G5 = TG5 := by decide +kernel
theorem g_F : trM (CFSG.KC.LL.HN.subI F) = GF := by decide +kernel
theorem t_I : trM I0 = TI0 ∧ trM I1 = TI1 ∧ trM I2 = TI2 ∧ trM I3 = TI3 ∧ trM I4 = TI4 ∧
    trM I5 = TI5 := by decide +kernel
theorem t_E : trM E0 = TE0 ∧ trM E1 = TE1 ∧ trM E2 = TE2 ∧ trM E3 = TE3 := by decide +kernel

theorem cm_F : mm F I0 = mm I0 F ∧ mm F I1 = mm I1 F ∧ mm F I2 = mm I2 F ∧ mm F I3 = mm I3 F ∧
    mm F I4 = mm I4 F ∧ mm F G5 = mm G5 F := by decide +kernel

theorem fx : ptsFn TX MS CM3 M TF om om 50 = true := by decide +kernel

theorem rs_I : omImg TI0 (lgetL IS 0) = true ∧ omImg TI1 (lgetL IS 1) = true ∧
    omImg TI2 (lgetL IS 2) = true ∧ omImg TI3 (lgetL IS 3) = true ∧
    omImg TI4 (lgetL IS 4) = true ∧ omImg TI5 (lgetL IS 5) = true := by decide +kernel
theorem rs_E : omImg TE0 (lgetL ES6 0) = true ∧ omImg TE1 (lgetL ES6 1) = true ∧
    omImg TE2 (lgetL ES6 2) = true ∧ omImg TE3 (lgetL ES6 3) = true := by decide +kernel

theorem sch : schOk IS TW IDS = true := by decide +kernel

theorem ids : idsAt 0 = true ∧ idsAt 1 = true ∧ idsAt 2 = true ∧ idsAt 3 = true := by
  decide +kernel

theorem neg_fx : Bool.not (ptsFn TX MS CM3 M TI0 om om 50) = true := by decide +kernel
theorem neg_rs : Bool.not (omImg TI1 (lgetL IS 0)) = true := by decide +kernel
theorem neg_cm : Bool.not (Nat.beq (mm F (R 34)) (mm (R 34) F)) = true := by decide +kernel
theorem neg_sch : Bool.not (schOk IS TW IDS.tail) = true := by decide +kernel
theorem neg_ids : Bool.not (idsOk src dst TW IS (lget CH 1) IDS (lgetL ST 0)) = true := by
  decide +kernel

end CertificateChecks.KernelSporSch.HNPt2085

end
