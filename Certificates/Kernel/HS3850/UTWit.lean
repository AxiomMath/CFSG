module

public import Certificates.Kernel.HS3850.UTDefs
public import Certificates.Kernel.LocalQT.SV.C4126T
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.ConjOrb
public import Certificates.Data.Kernel.PkPow

set_option maxRecDepth 400000
set_option Elab.async false

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KC.InvTabK
open CFSG.Quasithin.B45Exc.HS CFSG.Quasithin.B45Exc.Tab

@[expose] noncomputable def L0 : List Nat := [HS.F 0, HS.F 1]

@[expose] noncomputable def LI0 : List Nat := [HSI 0, HSI 1]

@[expose] noncomputable def pwK (e Y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idn (fun _ acc => pc Y acc) e

@[expose] noncomputable def regL (B : List Nat) (G GI : Nat) : List Nat :=
  B.map xE ++ B.map fun i => pc (pc G (xE i)) GI

@[expose] noncomputable def regLI (B : List Nat) (G GI : Nat) : List Nat :=
  B.map xE ++ B.map fun i => pc G (pc (xE i) GI)

@[expose] noncomputable def genK (w : GenWit) : Bool :=
  strictB (wordP1 3850 12 L0 LI0 w.g) fun G => strictB (wordP2 3850 12 L0 LI0 w.g) fun GI =>
    w.basis.all (fun i => Nat.blt i 191) && Nat.beq w.ws.length 2 &&
      (List.zip w.ws L0).all fun p =>
        Nat.beq (wordP1 3850 12 (regL w.basis G GI) (regLI w.basis G GI) p.1) p.2

@[expose] noncomputable def dimK (w : DimWit) : Bool :=
  strictB (wordP1 3850 12 L0 LI0 w.g) fun G => strictB (wordP2 3850 12 L0 LI0 w.g) fun GI =>
    strictB (pc (pc (pc G (xE w.e)) GI) (xE w.e')) fun Y =>
    Nat.blt w.d 191 && Nat.blt w.c 191 && Nat.blt w.e 191 && Nat.blt w.e' 191 &&
      Nat.beq (FX w.d) 46 && Nat.beq (FX w.c) 350 &&
      (Nat.beq (FX w.e) 170 || Nat.beq (FX w.e) 30) &&
      (Nat.beq (FX w.e') 170 || Nat.beq (FX w.e') 30) &&
      Nat.beq (pc G (xE w.c)) (pc (xE w.c) G) && Nat.beq (pwK 5 Y) idn && !(Nat.beq Y idn)

theorem gcanon : allN 2 (fun k => canonK 3850 12 (mask 12) (3850 * 12) (HS.F k) &&
    canonK 3850 12 (mask 12) (3850 * 12) (HSI k)) = true := by quickRfl

theorem genW0 : genK (hsGenWits[0]'(by decide)) = true := by quickRfl
theorem genW1 : genK (hsGenWits[1]'(by decide)) = true := by quickRfl
theorem genW2 : genK (hsGenWits[2]'(by decide)) = true := by quickRfl
theorem genW3 : genK (hsGenWits[3]'(by decide)) = true := by quickRfl
theorem genW4 : genK (hsGenWits[4]'(by decide)) = true := by quickRfl
theorem genW5 : genK (hsGenWits[5]'(by decide)) = true := by quickRfl
theorem genW6 : genK (hsGenWits[6]'(by decide)) = true := by quickRfl
theorem genW7 : genK (hsGenWits[7]'(by decide)) = true := by quickRfl
theorem genW8 : genK (hsGenWits[8]'(by decide)) = true := by quickRfl
theorem genW9 : genK (hsGenWits[9]'(by decide)) = true := by quickRfl
theorem genW10 : genK (hsGenWits[10]'(by decide)) = true := by quickRfl
theorem genW11 : genK (hsGenWits[11]'(by decide)) = true := by quickRfl
theorem genW12 : genK (hsGenWits[12]'(by decide)) = true := by quickRfl
theorem genW13 : genK (hsGenWits[13]'(by decide)) = true := by quickRfl
theorem genW14 : genK (hsGenWits[14]'(by decide)) = true := by quickRfl

theorem dimW0 : dimK (hsDimWits[0]'(by decide)) = true := by quickRfl
theorem dimW1 : dimK (hsDimWits[1]'(by decide)) = true := by quickRfl
theorem dimW2 : dimK (hsDimWits[2]'(by decide)) = true := by quickRfl
theorem dimW3 : dimK (hsDimWits[3]'(by decide)) = true := by quickRfl
theorem dimW4 : dimK (hsDimWits[4]'(by decide)) = true := by quickRfl
theorem dimW5 : dimK (hsDimWits[5]'(by decide)) = true := by quickRfl
theorem dimW6 : dimK (hsDimWits[6]'(by decide)) = true := by quickRfl
theorem dimW7 : dimK (hsDimWits[7]'(by decide)) = true := by quickRfl

theorem gen : hsGenWits.all genK = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < 15 := by
    have hl : hsGenWits.length = 15 := by decide
    omega
  interval_cases i
  exacts [genW0, genW1, genW2, genW3, genW4, genW5, genW6, genW7, genW8, genW9, genW10, genW11,
    genW12, genW13, genW14]

theorem dim : hsDimWits.all dimK = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < 8 := by
    have hl : hsDimWits.length = 8 := by decide
    omega
  interval_cases i
  exacts [dimW0, dimW1, dimW2, dimW3, dimW4, dimW5, dimW6, dimW7]

end CertificateChecks.KernelHS3850.UT

end
