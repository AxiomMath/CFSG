
module

public import Certificates.Data.Kernel.PermCent.L34MTwin
public import Certificates.Data.Kernel.PermCent.L34MSyl
public import CFSG.Certificates.Kernel.PermCent.CodeTabSound
public import Certificates.Data.Kernel.PermCent.L34OrbW
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.PermCent.L34CodesEval
meta import Certificates.Data.Kernel.PermCent.L34OrbA

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.L34MT

open CFSG.GH74.Uniqueness.SU.K.R4.L34M CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum

theorem kQP : schP QP = true := by decide +kernel

theorem kChars : charsOK W1.chars = true ∧ charsOK W2.chars = true ∧ charsOK W3.chars = true ∧
    charsOK W4.chars = true := by
  decide +kernel

@[expose] noncomputable def gAut : List (CV 42) := [cOf PA, cOf PB, cOf sg0, cOf sg1, cOf sg2]

@[expose] noncomputable def tGens : List (CV 42) := tGenW.map (SylL.wordC gAut)

@[expose] noncomputable def tElts : List (CV 42) := tEltW.map (SylL.wordC tGens)

@[expose] noncomputable def repsC : List (CV 42) := [cOf rep1, cOf rep2, cOf rep3, cOf rep4]

@[expose] noncomputable def conjAllC (s : CV 42) (L : List (CV 42)) :
    List (CV 42) → List Nat → Bool
  | [], _ => true
  | u :: M, k :: t => eq22C s u (L.getD k 1) s && conjAllC s L M t
  | _ :: _, [] => false

@[expose] noncomputable def conjOKC (L : List (CV 42)) : List (CV 42) → List (List Nat) → Bool
  | [], _ => true
  | s :: S, t :: T => conjAllC s L L t && conjOKC L S T
  | _ :: _, [] => false

theorem kSylClosed : SylL.closedC tGens tElts = true := by decide +kernel

theorem kSylCover : SylL.coverC gAut repsC tElts covW = true := by decide +kernel

theorem kSylLen : tElts.length = 2 ^ 8 := by decide +kernel

theorem kRep : decide (cOf rep1 ∈ clC rep1 W1.chars) = true ∧
    decide (cOf rep2 ∈ clC rep2 W2.chars) = true ∧ decide (cOf rep3 ∈ clC rep3 W3.chars) = true ∧
    decide (cOf rep4 ∈ clC rep4 W4.chars) = true := by
  decide +kernel

theorem kConj1 : conjOKC (clC rep1 W1.chars) gAut conjT1 = true := by decide +kernel

theorem kConj2 : conjOKC (clC rep2 W2.chars) gAut conjT2 = true := by decide +kernel

#kmisc_packarrs CFSG.Certificates.Kernel.PkCV.L34MT.X3 CFSG.Certificates.Kernel.PkCV.L34Ev.cl3A 6

theorem kTie3 : tieT X3 (clC rep3 W3.chars) 0 = true ∧ (clC rep3 W3.chars).length = 1008 := by
  decide +kernel

theorem kCls3 : ((List.range 5).all fun k => clsT (gAut.getD k 1) X3 1008 (conjT3.getD k []) 0) =
    true := by
  decide +kernel

theorem kConj4 : conjOKC (clC rep4 W4.chars) gAut conjT4 = true := by decide +kernel

@[expose] noncomputable def gP : List (CV 42) := [cOf PA, cOf PB]

#kmisc_packarrs CFSG.Certificates.Kernel.PkCV.L34MT.XO4 CFSG.Certificates.Kernel.PkCV.L34Orb.orbA4 6

theorem kOrb4 : orbTabOK gP (cOf rep4) L34Orb.orbW4 XO4 L34Orb.orbR4 = true := by decide +kernel

theorem kEAll : (siftP QP e4u0 0 = true ∧ siftP QP e4v0 0 = true ∧
    (decide (e4u0 ≠ 1) && decide (e4v0 ≠ 1) && decide (e4u0 ≠ e4v0) && decide (e4u0 ^ 2 = 1) &&
      decide (e4v0 ^ 2 = 1) && decide (e4u0 * e4v0 = e4v0 * e4u0) && decide (1 * e4u0 = e4u0 * 1) &&
      decide (1 * e4v0 = e4v0 * 1)) = true) ∧
    (siftP QP e4u1 0 = true ∧ siftP QP e4v1 0 = true ∧
    (decide (e4u1 ≠ 1) && decide (e4v1 ≠ 1) && decide (e4u1 ≠ e4v1) && decide (e4u1 ^ 2 = 1) &&
      decide (e4v1 ^ 2 = 1) && decide (e4u1 * e4v1 = e4v1 * e4u1) &&
      decide (rep1 * e4u1 = e4u1 * rep1) && decide (rep1 * e4v1 = e4v1 * rep1)) = true) ∧
    (siftP QP e4u2 0 = true ∧ siftP QP e4v2 0 = true ∧
    (decide (e4u2 ≠ 1) && decide (e4v2 ≠ 1) && decide (e4u2 ≠ e4v2) && decide (e4u2 ^ 2 = 1) &&
      decide (e4v2 ^ 2 = 1) && decide (e4u2 * e4v2 = e4v2 * e4u2) &&
      decide (rep2 * e4u2 = e4u2 * rep2) && decide (rep2 * e4v2 = e4v2 * rep2)) = true) ∧
    (siftP QP e4u3 0 = true ∧ siftP QP e4v3 0 = true ∧
    (decide (e4u3 ≠ 1) && decide (e4v3 ≠ 1) && decide (e4u3 ≠ e4v3) && decide (e4u3 ^ 2 = 1) &&
      decide (e4v3 ^ 2 = 1) && decide (e4u3 * e4v3 = e4v3 * e4u3) &&
      decide (rep3 * e4u3 = e4u3 * rep3) && decide (rep3 * e4v3 = e4v3 * rep3)) = true) := by
  decide +kernel

theorem kE0 : siftP QP e4u0 0 = true ∧ siftP QP e4v0 0 = true ∧
    (decide (e4u0 ≠ 1) && decide (e4v0 ≠ 1) && decide (e4u0 ≠ e4v0) && decide (e4u0 ^ 2 = 1) &&
      decide (e4v0 ^ 2 = 1) && decide (e4u0 * e4v0 = e4v0 * e4u0) && decide (1 * e4u0 = e4u0 * 1) &&
      decide (1 * e4v0 = e4v0 * 1)) = true :=
  kEAll.1

theorem kE1 : siftP QP e4u1 0 = true ∧ siftP QP e4v1 0 = true ∧
    (decide (e4u1 ≠ 1) && decide (e4v1 ≠ 1) && decide (e4u1 ≠ e4v1) && decide (e4u1 ^ 2 = 1) &&
      decide (e4v1 ^ 2 = 1) && decide (e4u1 * e4v1 = e4v1 * e4u1) &&
      decide (rep1 * e4u1 = e4u1 * rep1) && decide (rep1 * e4v1 = e4v1 * rep1)) = true :=
  kEAll.2.1

theorem kE2 : siftP QP e4u2 0 = true ∧ siftP QP e4v2 0 = true ∧
    (decide (e4u2 ≠ 1) && decide (e4v2 ≠ 1) && decide (e4u2 ≠ e4v2) && decide (e4u2 ^ 2 = 1) &&
      decide (e4v2 ^ 2 = 1) && decide (e4u2 * e4v2 = e4v2 * e4u2) &&
      decide (rep2 * e4u2 = e4u2 * rep2) && decide (rep2 * e4v2 = e4v2 * rep2)) = true :=
  kEAll.2.2.1

theorem kE3 : siftP QP e4u3 0 = true ∧ siftP QP e4v3 0 = true ∧
    (decide (e4u3 ≠ 1) && decide (e4v3 ≠ 1) && decide (e4u3 ≠ e4v3) && decide (e4u3 ^ 2 = 1) &&
      decide (e4v3 ^ 2 = 1) && decide (e4u3 * e4v3 = e4v3 * e4u3) &&
      decide (rep3 * e4u3 = e4u3 * rep3) && decide (rep3 * e4v3 = e4v3 * rep3)) = true :=
  kEAll.2.2.2

theorem kNegT : (tElts.all fun g => !powOneC g 2 || decide (g = 1) ||
      decide (g ∈ clC rep1 W1.chars)) = false := by
  decide +kernel

end CFSG.Certificates.Kernel.PkCV.L34MT
