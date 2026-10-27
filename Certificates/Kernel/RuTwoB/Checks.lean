module

public import Certificates.Kernel.SporSch.Ru.Wit
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.RuTwoBInputs
public import CFSG.Certificates.Kernel.Spor.MoveK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuTwoB

open CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.RuInv CFSG.KS.MoveK CertificateChecks.KernelSporSch
  CFSG.EvenSporadicStandard.RuStd.S2

@[expose] noncomputable def GP : Nat := wordP RuW.LG RuW.LGI twoBWordG

@[expose] noncomputable def HP : Nat := wordP RuW.LG RuW.LGI twoBWordH

@[expose] noncomputable def UP : Nat := wordP RuW.LG RuW.LGI twoBWordU

@[expose] noncomputable def CP : Nat := mulP (mulP (mulP GP HP) (invP GP)) (invP HP)

@[expose] noncomputable def invOK24942 : Bool := bAnd(RuG.pk GP (invP GP), RuG.pk HP (invP HP))

@[expose] noncomputable def commOK24942 : Bool :=
  strictB CP fun C => strictB (mulP C C) fun C2 =>
    bAnd(Nat.beq (mulP C (mulP C2 C2)) idP, difK (apP C) (fun i => i) 4060)

@[expose] noncomputable def uOK24942 : Bool :=
  strictB UP fun U =>
    bAnd(Nat.beq (mulP U U) idP, bAnd(difK (apP U) (fun i => i) 4060,
      bAnd(difK (apP U) (apP RuG.A0) 4060, bAnd(Nat.beq (mulP U (RuW.LG 0)) (mulP (RuW.LG 0) U),
        bAnd(Nat.beq (mulP U (RuW.LG 1)) (mulP (RuW.LG 1) U),
          Nat.beq (mulP U (RuW.LG 2)) (mulP (RuW.LG 2) U))))))

theorem ch24942_inv : invOK24942 = true := by quickRfl

theorem ch24942_comm : commOK24942 = true := by quickRfl

theorem ch24942_u : uOK24942 = true := by quickRfl

end CertificateChecks.KernelRuTwoB
