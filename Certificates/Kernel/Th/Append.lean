module

public import Certificates.Kernel.Co2.Join
public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.DceS
public import CFSG.Certificates.Kernel.Th.S.OutS
public import CFSG.Certificates.Kernel.Th.S.TsS
public meta import Lean

public section

namespace CertificateChecks.KernelTh

open CFSG.KC CFSG.KC.Loop CertificateChecks.KernelCo2

theorem andB_true {a b : Bool} (ha : a = true) (hb : b = true) : CFSG.KC.Th.andB a b = true := by
  subst ha
  exact hb

@[expose] noncomputable def foldS (step : Nat → Nat → Nat) (Cs : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun C _ ih S => strictN (step C S) ih) Cs

theorem foldS_append (step : Nat → Nat → Nat) :
    ∀ l1 l2 x, foldS step (List.append l1 l2) x = foldS step l2 (foldS step l1 x)
  | [], _, _ => rfl
  | C :: l1, l2, x => by
    change strictN (step C x) (foldS step (List.append l1 l2)) =
      foldS step l2 (strictN (step C x) (foldS step l1))
    rw [strictN_eq, strictN_eq, foldS_append step l1 l2]

open CFSG.KC.Th

theorem decodeRun_append (F : Nat → Nat) (lb M : Nat) :
    ∀ l1 l2 x, BigS.decodeRun F lb M (List.append l1 l2) x =
      BigS.decodeRun F lb M l2 (BigS.decodeRun F lb M l1 x) :=
  foldS_append _

theorem runSlp_append (RB : Nat → Nat) (c rm ONE : Nat) :
    ∀ l1 l2 x, BigS.runSlp RB c rm ONE (List.append l1 l2) x =
      BigS.runSlp RB c rm ONE l2 (BigS.runSlp RB c rm ONE l1 x) :=
  foldS_append _

theorem runPc_append (RB PW : Nat → Nat) (c rm ONE PR n p pb : Nat) :
    ∀ l1 l2 x, BigS.runPc RB PW c rm ONE PR n p pb (List.append l1 l2) x =
      BigS.runPc RB PW c rm ONE PR n p pb l2 (BigS.runPc RB PW c rm ONE PR n p pb l1 x) :=
  foldS_append _

theorem runTree_append (RB PT : Nat → Nat) (rm PR fr to : Nat) :
    ∀ l1 l2 x, BigS.runTree RB PT rm PR fr to (List.append l1 l2) x =
      BigS.runTree RB PT rm PR fr to l2 (BigS.runTree RB PT rm PR fr to l1 x) :=
  foldS_append _

theorem runPlanes_append (rm A Bi B root Cb : Nat) :
    ∀ l1 l2 x, BigS.runPlanes rm A Bi B root Cb (List.append l1 l2) x =
      BigS.runPlanes rm A Bi B root Cb l2 (BigS.runPlanes rm A Bi B root Cb l1 x) :=
  foldS_append _

theorem runHdr_append (HB FA : Nat → Nat) (LT TL VL NL shA wdA NFA : Nat) :
    ∀ l1 l2 x, DceS.runHdr HB FA LT TL VL NL shA wdA NFA (List.append l1 l2) x =
      DceS.runHdr HB FA LT TL VL NL shA wdA NFA l2 (DceS.runHdr HB FA LT TL VL NL shA wdA NFA l1 x) :=
  foldS_append _

theorem runGom_append (HB GB OB : Nat → Nat) (osh owd om NB sel I0 nH : Nat) :
    ∀ l1 l2 x, DceS.runGom HB GB OB osh owd om NB sel I0 nH (List.append l1 l2) x =
      DceS.runGom HB GB OB osh owd om NB sel I0 nH l2 (DceS.runGom HB GB OB osh owd om NB sel I0 nH l1 x) :=
  foldS_append _

theorem runSorted_append (get : Nat → Nat) (qb m : Nat) :
    ∀ l1 l2 x, DceS.runSorted get qb m (List.append l1 l2) x =
      DceS.runSorted get qb m l2 (DceS.runSorted get qb m l1 x) :=
  foldS_append _

theorem runCover_append (FB OB : Nat → Nat) (sh wd osh owd om NB sel NF NO AL : Nat) :
    ∀ l1 l2 x, DceS.runCover FB OB sh wd osh owd om NB sel NF NO AL (List.append l1 l2) x =
      DceS.runCover FB OB sh wd osh owd om NB sel NF NO AL l2
        (DceS.runCover FB OB sh wd osh owd om NB sel NF NO AL l1 x) :=
  foldS_append _

theorem runStab_append (FB EB : Nat → Nat) (sh wd NF D SG : Nat) :
    ∀ l1 l2 x, DceS.runStab FB EB sh wd NF D SG (List.append l1 l2) x =
      DceS.runStab FB EB sh wd NF D SG l2 (DceS.runStab FB EB sh wd NF D SG l1 x) :=
  foldS_append _

theorem runClass_append (CB : Nat → Nat) (LT LI TL VL NL : Nat) :
    ∀ l1 l2 x, DceS.runClass CB LT LI TL VL NL (List.append l1 l2) x =
      DceS.runClass CB LT LI TL VL NL l2 (DceS.runClass CB LT LI TL VL NL l1 x) :=
  foldS_append _

theorem runFacts_append (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (el : Bool) :
    ∀ l1 l2 x, DceS.runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi el (List.append l1 l2) x =
      DceS.runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi el l2
        (DceS.runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi el l1 x) :=
  foldS_append _

theorem runT_append (HB TB OB RR FA : Nat → Nat)
    (LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA : Nat) :
    ∀ l1 l2 x, DceS.runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA
        (List.append l1 l2) x =
      DceS.runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA l2
        (DceS.runT HB TB OB RR FA LT TL VL NL NR nH nT osh owd om NB sel I0 shA wdA NFA l1 x) :=
  foldS_append _

theorem runItems_append (f : Nat → Bool) :
    ∀ l1 l2 x, TsS.runItems f (List.append l1 l2) x = TsS.runItems f l2 (TsS.runItems f l1 x) :=
  foldS_append _

theorem runClass2_append (CB : Nat → Nat) (LT LI TL VL NL : Nat) :
    ∀ l1 l2 x, OutS.runClass2 CB LT LI TL VL NL (List.append l1 l2) x =
      OutS.runClass2 CB LT LI TL VL NL l2 (OutS.runClass2 CB LT LI TL VL NL l1 x) :=
  foldS_append _

end CertificateChecks.KernelTh

namespace CertificateChecks.KernelTh.Thm

open Lean Elab Command Term Meta

elab "kernel_exact " v:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let e ← Lean.Elab.Tactic.elabTerm v none
    let e ← instantiateMVars e
    if e.hasMVar then throwError "kernel_exact: the term has metavariables{indentExpr e}"
    g.assign e
    Lean.Elab.Tactic.replaceMainGoal []

elab "#th_list_of " nm:ident thm:ident : command => do
  let name := (← getCurrNamespace) ++ nm.getId
  let t ← liftCoreM <| realizeGlobalConstNoOverload thm
  let some ci := (← getEnv).find? t | throwError "unknown theorem {t}"
  let some (_, l, _, _) := CertificateChecks.KernelCo2.Join.parts ci.type
    | throwError "{t}: not a slice check"
  let ty := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let d : DefinitionVal := { name, levelParams := [], type := ty, value := l, hints := .regular 0, safety := .safe }
  liftCoreM <| withOptions (Elab.async.set · false) <| addDecl (.defnDecl d)

end CertificateChecks.KernelTh.Thm
