module

public import Certificates.Kernel.SporSch.Ru.Wit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzInputs
public import CFSG.Certificates.Kernel.Spor.MoveK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuSz

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KS.MoveK CertificateChecks.KernelSporSch
  CFSG.EvenSporadicStandard.Induction.RuSz

@[expose] noncomputable def SP : Nat := wordP RuW.LG RuW.LGI sWord

@[expose] noncomputable def TP : Nat := wordP RuW.LG RuW.LGI tWord

@[expose] noncomputable def BP : Nat := wordP RuW.LG RuW.LGI bWord

@[expose] noncomputable def letST (S SI T TI : Nat) (l : Nat × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nIf(Nat.beq l.1 (nat_lit 0), SI, TI))
    (nIf(Nat.beq l.1 (nat_lit 0), S, T)) l.2

@[expose] noncomputable def wordST (S SI T TI : Nat) (v : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat) idP
    (fun l _ ih => strictN ih fun X => mulP (letST S SI T TI l) X) v

@[expose] noncomputable def invOK' : Bool := bAnd(RuG.pk SP (invP SP), RuG.pk TP (invP TP))

@[expose] noncomputable def relOK : Bool :=
  strictB SP fun S => strictB (invP SP) fun SI => strictB TP fun T => strictB (invP TP) fun TI =>
    szRels.all fun v => Nat.beq (wordST S SI T TI v) idP

@[expose] noncomputable def ntOK : Bool := strictB SP fun S => difK (apP S) (fun i => i) 4060

@[expose] noncomputable def normOK : Bool :=
  strictB SP fun S => strictB (invP SP) fun SI => strictB TP fun T => strictB (invP TP) fun TI =>
    normWords.all fun c => Nat.beq (mulP (mulP (RuW.LG c.1) (if c.2.1 then T else S)) (RuW.LGI c.1))
      (wordST S SI T TI (parseW c.2.2))

@[expose] noncomputable def centOK : Bool :=
  strictB SP fun S => strictB TP fun T => strictB BP fun B =>
    bAnd(Nat.beq (mulP B B) idP, bAnd(difK (apP B) (fun i => i) 4060,
      bAnd(difK (apP B) (apP RuG.A0) 4060, bAnd(Nat.beq (mulP B S) (mulP S B),
        Nat.beq (mulP B T) (mulP T B)))))

@[expose] noncomputable def fixOK : Bool :=
  strictB SP fun S => strictB (invP SP) fun SI => strictB TP fun T => strictB (invP TP) fun TI =>
  strictB (wordST S SI T TI (parseW (hWords.getD 0 ""))) fun H0 =>
  strictB (wordST S SI T TI (parseW (hWords.getD 1 ""))) fun H1 =>
  strictB (wordST S SI T TI (parseW (hWords.getD 2 ""))) fun H2 =>
    bAnd(Nat.beq (apP H0 0) 0, bAnd(Nat.beq (apP H1 0) 0, bAnd(Nat.beq (apP H2 0) 0,
      (List.range 4060).filter (fun x =>
        bAnd(Nat.beq (apP H0 x) x, bAnd(Nat.beq (apP H1 x) x, Nat.beq (apP H2 x) x))) ==
        [0, 1, 3645, 3692])))

@[expose] noncomputable def ptOK : Bool :=
  strictB SP fun S => strictB (invP SP) fun SI => strictB TP fun T => strictB (invP TP) fun TI =>
    ptWords.all fun c => Nat.beq (apP (wordST S SI T TI (parseW c.2)) 0) c.1

theorem inv_ok : invOK' = true := by quickRfl
theorem rel_ok : relOK = true := by quickRfl
theorem nt_ok : ntOK = true := by quickRfl
theorem norm_ok : normOK = true := by quickRfl
theorem cent_ok : centOK = true := by quickRfl
theorem fix_ok : fixOK = true := by quickRfl
theorem pt_ok : ptOK = true := by quickRfl

end CertificateChecks.KernelRuSz

end
