module

public import Certificates.Kernel.SporSch.HN.Prim2104Data
public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Data.Kernel.SporSch.HNXSub
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import Certificates.Kernel.SporSch.HN.PrimK.I0
public import Certificates.Kernel.SporSch.HN.PrimK.I1
public import Certificates.Kernel.SporSch.HN.PrimK.O0
public import Certificates.Kernel.SporSch.HN.PrimK.O1
public import Certificates.Kernel.SporSch.HN.PrimK.N
public import CFSG.Certificates.Kernel.Common.ForallBlocks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPrim2104

open CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KD.LgHNX CFSG.KD.HNPrim CFSG.KC.ForallBlocks CFSG.KD.HNXK

theorem img_all : ∀ k < 379, imgRange TX UT CM3 M TR1 CFSG.KD.OrdHN.ONE 21 (47 * k) 47 = true :=
  forall_of_blocks (R := 192) (G := 2) (by decide) (by decide) fun j hj =>
    match j, hj with
    | 0, _ => fun i hi _ => I0.all i hi
    | 1, _ => fun i _ h => I1.all i (by change i < 187; omega)
    | _ + 2, h => absurd h (by omega)

theorem orb_all : ∀ k < 379, orbRange UT REPS (47 * k) 47 = true :=
  forall_of_blocks (R := 192) (G := 2) (by decide) (by decide) fun j hj =>
    match j, hj with
    | 0, _ => fun i hi _ => O0.all i hi
    | 1, _ => fun i _ h => O1.all i (by change i < 187; omega)
    | _ + 2, h => absurd h (by omega)

theorem eq_all : ∀ k < 379, eqRange TX UT (47 * k) 47 = true :=
  forall_of_blocks (R := 192) (G := 2) (by decide) (by decide) fun j hj =>
    match j, hj with
    | 0, _ => fun i hi _ => A0.all i hi
    | 1, _ => fun i _ h => A1.all i (by change i < 187; omega)
    | _ + 2, h => absurd h (by omega)

theorem tr_R1 : Nat.beq (trM (CFSG.KD.HNPt.R 1)) TR1 = true := by quickRfl
theorem tr_one : Nat.beq (trM CFSG.KD.OrdHN.ONE) CFSG.KD.OrdHN.ONE = true := by quickRfl

theorem lab_reps : CFSG.KC.Enum.allN 12 (fun j => Nat.beq (labOf UT (fldW REPS (21 * j) 21)) j) =
    true := by quickRfl

theorem rec_zero1 : Nat.beq (fldW (getRec UT 76 0) 0 21) 0 = true := by quickRfl
theorem rec_zero2 : Nat.beq (fldW (getRec UT 76 0) 21 21) 0 = true := by quickRfl

theorem neg_img : Bool.not (imgLeaf TX UT CM3 M (trM (CFSG.KD.HNPt.R 0)) CFSG.KD.OrdHN.ONE 21 5) =
    true := by quickRfl
theorem neg_img1 : Bool.not (imgLeaf TX (fun b => UT (Nat.add b 1)) CM3 M TR1 CFSG.KD.OrdHN.ONE 21 5) =
    true := by quickRfl
theorem neg_eq : Bool.not (eqLeaf TX (fun b => UT (Nat.add b 1)) 5) = true := by quickRfl
theorem neg_orb_u : Bool.not (orbRec UT REPS 70 (Nat.add (getRec UT 76 70) 1)) = true := by quickRfl
theorem neg_orb_lab : Bool.not (orbRec UT REPS 70
    (Nat.add (getRec UT 76 70) (Nat.shiftLeft 1 42))) = true := by quickRfl
theorem neg_orb_dep : Bool.not (orbRec UT REPS 70
    (Nat.add (getRec UT 76 70) (Nat.shiftLeft 1 46))) = true := by quickRfl
theorem neg_orb_par : Bool.not (orbRec UT REPS 70
    (Nat.add (getRec UT 76 70) (Nat.shiftLeft 1 54))) = true := by quickRfl
theorem neg_orb_root : Bool.not (orbRec UT REPS 1 (Nat.add (getRec UT 76 1) (Nat.shiftLeft 1 46))) =
    true := by quickRfl
theorem neg_cnt : Bool.not (Nat.beq (cntSum UT 0 47) (cntSum UT 47 47)) = true := by quickRfl
theorem neg_reps : Bool.not (Nat.beq (labOf UT (fldW REPS (21 * 3) 21)) 4) = true := by quickRfl

end CertificateChecks.KernelSporSch.HNPrim2104

end
