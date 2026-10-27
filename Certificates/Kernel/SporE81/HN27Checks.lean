module

public import Certificates.Kernel.SporE81.HN27Data
public import Certificates.Kernel.SporSch.HN.Pt2108Defs
public import Certificates.Kernel.LocalQT.Tc.Gen
public import CFSG.Mathlib.Decide.Nodup
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE81.HN27K

open CFSG.KC.Enum CFSG.KC.LL CFSG.Sporadic.HNSchreier CFSG.KD.HN27
open CertificateChecks.KernelSporSch.HNPt2108

@[expose] def cG (j : Nat) : Nat := cond (Nat.beq j 4) 1 0

@[expose] def fld2 (P i : Nat) : Nat := Nat.land (Nat.shiftRight P (Nat.mul 2 i)) 3

@[expose] def fld10 (Q i : Nat) : Nat := Nat.land (Nat.shiftRight Q (Nat.mul 10 i)) 1023

@[expose] noncomputable def lamGo (l : List (Nat × Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ P => P)
    (fun pj _ ih i P => strictN (Nat.lor P (Nat.shiftLeft
      (Nat.mod (Nat.add (fld2 P pj.1) (cG pj.2)) 3) (Nat.mul 2 i))) fun Q =>
        strictN (Nat.succ i) fun j => ih j Q) l

@[expose] noncomputable def lamP : Nat := lamGo FAData.pParents.toList 0 0

@[expose] noncomputable def packGo (l : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ Q => Q)
    (fun x _ ih i Q => strictN (Nat.lor Q (Nat.shiftLeft x (Nat.mul 10 i))) fun R =>
      strictN (Nat.succ i) fun j => ih j R) l

@[expose] noncomputable def rowP (j : Nat) : Nat := packGo (FAData.pLeft[j]!).toList 0 0

@[expose] noncomputable def lamRow (P c : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => Nat.beq (fld2 P x) (Nat.mod (Nat.add (fld2 P i) c) 3) && ih (Nat.succ i)) l

@[expose] noncomputable def rowChk (Q : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => Nat.beq (fld10 Q i) x && ih (Nat.succ i)) l

@[expose] def itR (Q n x : Nat) : Nat := Nat.rec (motive := fun _ => Nat) x (fun _ y => fld10 Q y) n

@[expose] def dIdx (Q1 Q3 Q4 Q5 n : Nat) : Nat :=
  itR Q1 (n / 27) (itR Q3 (n / 9 % 3) (itR Q4 (n / 3 % 3) (itR Q5 (n % 3) 0)))

@[expose] def dList (Q1 Q3 Q4 Q5 : Nat) : List Nat := (List.range 81).map (dIdx Q1 Q3 Q4 Q5)

@[expose] def labZ (P i : Nat) : Bool := Nat.beq (Nat.mod (fld2 P i) 3) 0

@[expose] noncomputable def clsOK (P z1 z2 : Nat) (l : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun cl _ ih c => (WC.contains c || cl.all fun i =>
      !labZ P i || Nat.beq i z1 || Nat.beq i z2) && ih (Nat.succ c)) l

@[expose] def gComm (Qa Qb : Nat) : Bool := Nat.beq (itR Qa 1 (itR Qb 1 0)) (itR Qb 1 (itR Qa 1 0))

@[expose] noncomputable def mainK (P Q1 Q3 Q4 Q5 : Nat) : Bool :=
  CFSG.Decide.bitsetNodup (dList Q1 Q3 Q4 Q5) &&
  gComm Q1 Q3 && gComm Q1 Q4 && gComm Q1 Q5 && gComm Q3 Q4 && gComm Q3 Q5 && gComm Q4 Q5 &&
  Nat.beq (itR Q1 3 0) 0 && Nat.beq (itR Q3 3 0) 0 && Nat.beq (itR Q4 3 0) 0 &&
  Nat.beq (itR Q5 3 0) 0 && !Nat.beq (itR Q5 1 0) 0 &&
  WT.all (fun t => (dList Q1 Q3 Q4 Q5).contains t) &&
  clsOK P (itR Q5 1 0) (itR Q5 2 0) FAData.wClass.toList 0

@[expose] noncomputable def witK (c : Nat) (w : List Nat) (t : Nat) : Bool :=
  strictB (liftM w) fun W =>
    Nat.beq (CFSG.KC.LL.HN.mm W (EM FAData.wRep[c]!)) (CFSG.KC.LL.HN.mm (EM t) W)

@[expose] noncomputable def wS (k : Nat) : Bool := witK (WC.getD k 0) (WW.getD k []) (WT.getD k 0)

theorem lam_ok : strictB lamP (fun P => Nat.beq (fld2 P 0) 0 &&
    (List.range 6).all fun j => lamRow P (cG j) (FAData.pLeft[j]!).toList 0) = true := by
  quickRfl

theorem cnt_ok : strictB lamP (fun P =>
    Nat.beq ((List.range 729).filter (labZ P)).length 243) = true := by
  quickRfl

theorem rows_ok : [1, 3, 4, 5].all (fun j => strictB (rowP j) fun Q =>
    rowChk Q (FAData.pLeft[j]!).toList 0) = true := by
  quickRfl

theorem main_ok : strictB lamP (fun P => strictB (rowP 1) fun Q1 => strictB (rowP 3) fun Q3 =>
    strictB (rowP 4) fun Q4 => strictB (rowP 5) fun Q5 => mainK P Q1 Q3 Q4 Q5) = true := by
  quickRfl

theorem wit_data : WC.length = 32 ∧ WW.length = 32 ∧ WT.length = 32 ∧ (∀ c ∈ WC, c < 48) ∧
    ∀ w ∈ WW, ∀ l ∈ w, 1 ≤ l ∧ l ≤ 7 := by
  decide +kernel

end CertificateChecks.KernelE81.HN27K

set_option Elab.async false

#kqb_range CertificateChecks.KernelE81.HN27K.witC CertificateChecks.KernelE81.HN27K.wS 0 32
#kqb_all CertificateChecks.KernelE81.HN27K.witC CertificateChecks.KernelE81.HN27K.wS 32

end
