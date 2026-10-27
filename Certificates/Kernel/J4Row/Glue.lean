module

public import Certificates.Kernel.J4Row.Checks
public import Certificates.Kernel.J4NPVerdict.Glue
public import CFSG.Certificates.Kernel.J4Row.Sound
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4Data
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import Certificates.Kernel.J4Count.FixCE

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Row

open CFSG.Sporadic.J4 CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.J4NPV
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4 (RowFactsJ)
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (starMasks)

local notation "R31" => CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4.row31
local notation "R43" => CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.SimsSporJ4.row43

theorem us_rep : ∀ j < 11, VjRep (getN one us j) (QT.uJ j) := by
  intro j hj
  have h := CertificateChecks.KernelJ4Q.uTab_enc j (by rw [CertificateChecks.KernelJ4Q.Us_length]; exact hj)
  exact CertificateChecks.KernelJ4NPV.vjg_rep h (QT.Mx_uJ CertificateChecks.KernelJ4Q.matFacts hj)

theorem eta_rep : ∀ m, VjRep (etaK c rm one us m) (QT.eta QT.uJ 11 m) := fun m =>
  CertificateChecks.KernelJ4NPV.vjg_rep (CertificateChecks.KernelJ4Q.eta_enc m)
    (QT.Mx_eta CertificateChecks.KernelJ4Q.matFacts 11 le_rfl m)

theorem facts_of_chk {prog : List (Nat × Nat × Nat)} {p m n rz ru : Nat} {gens cols : List Nat}
    {bfs : List (Nat × Nat)} {N : Nat} (h : chk prog p m n rz ru gens cols bfs N = true) :
    ∃ z u : J, ∃ L : List J, RowFactsJ p m n (getN 0 cols) N z u L :=
  CFSG.KC.J4Row.rowChkK_sound CertificateChecks.KernelJ4Q.hK us_rep eta_rep
    (CertificateChecks.KernelJ4NPV.vjg_base 0) (CertificateChecks.KernelJ4NPV.vjg_basei 0)
    (CertificateChecks.KernelJ4NPV.vjg_base 1) (CertificateChecks.KernelJ4NPV.vjg_basei 1) h

theorem row_facts {p m n N ce : Nat} {cols pi : List Nat} {col : ℕ → ℕ}
    {π : Equiv.Perm (Fin 24)} (hcol : getN 0 cols = col)
    (hpi : ∀ i : Fin 24, getN 0 pi i = (π i : ℕ))
    (hR : ∃ z u : J, ∃ L : List J, RowFactsJ p m n (getN 0 cols) N z u L)
    (hm : CFSG.KC.J4Row.maskChkK cols pi starMasks = true)
    (hc : Nat.beq (CFSG.KC.J4Row.ceCntK cols) ce = true) :
    (∃ z u : J, ∃ L : List J, RowFactsJ p m n col N z u L) ∧
      (∀ j, col j < 2 ^ 11) ∧
      (∀ i : Fin 24, ∀ c ∈ starMasks.getD i [], QT.rowsXor col 11 c ∈ starMasks.getD (π i) []) ∧
      (∀ i < 24, 1 ∈ starMasks.getD i [] → i = 4 ∨ i = 11) ∧
      1 ∈ starMasks.getD 4 [] ∧ 1 ∈ starMasks.getD 11 [] ∧
      ((Finset.range 2048).filter fun c => QT.rowsXor col 11 c = c).card = ce := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := CFSG.KC.J4Row.maskChkK_facts hm
  rw [hcol] at hR h1 h2
  refine ⟨hR, h1, fun i c hc' => ?_, h3, h4, h5, ?_⟩
  · rw [← hpi i]
    exact h2 i i.2 c hc'
  · rw [← hcol, ← CFSG.KC.J4Row.ceCntK_eq]
    exact Nat.eq_of_beq_eq_true hc

theorem cols31 : getN 0 CFSG.KD.J4Row.r31cols = (R31).col := by
  funext j
  rw [CFSG.KC.J4Row.getN_getD]
  have e : CFSG.KD.J4Row.r31cols = (R31).cols := by decide +kernel
  rw [e]
  rfl

theorem cols43 : getN 0 CFSG.KD.J4Row.r43cols = (R43).col := by
  funext j
  rw [CFSG.KC.J4Row.getN_getD]
  have e : CFSG.KD.J4Row.r43cols = (R43).cols := by decide +kernel
  rw [e]
  rfl

theorem pi31 : ∀ i : Fin 24, getN 0 CFSG.KD.J4Row.r31pi i = ((R31).piPerm i : ℕ) := by
  decide +kernel

theorem pi43 : ∀ i : Fin 24, getN 0 CFSG.KD.J4Row.r43pi i = ((R43).piPerm i : ℕ) := by
  decide +kernel

theorem n31 : CFSG.KD.J4Row.r31N = 80 := by decide +kernel

theorem n43 : CFSG.KD.J4Row.r43N = 56 := by decide +kernel

theorem facts31 :
    (∃ z u : J, ∃ L : List J, RowFactsJ 31 27 10 (R31).col 80 z u L) ∧
      (∀ j, (R31).col j < 2 ^ 11) ∧
      (∀ i : Fin 24, ∀ c ∈ starMasks.getD i [],
        QT.rowsXor (R31).col 11 c ∈ starMasks.getD ((R31).piPerm i) []) ∧
      (∀ i < 24, 1 ∈ starMasks.getD i [] → i = 4 ∨ i = 11) ∧
      1 ∈ starMasks.getD 4 [] ∧ 1 ∈ starMasks.getD 11 [] ∧
      ((Finset.range 2048).filter fun c => QT.rowsXor (R31).col 11 c = c).card = 8 := by
  have hR := facts_of_chk row31
  rw [n31] at hR
  exact row_facts cols31 pi31 hR mask31 ce31

theorem facts43 :
    (∃ z u : J, ∃ L : List J, RowFactsJ 43 22 14 (R43).col 56 z u L) ∧
      (∀ j, (R43).col j < 2 ^ 11) ∧
      (∀ i : Fin 24, ∀ c ∈ starMasks.getD i [],
        QT.rowsXor (R43).col 11 c ∈ starMasks.getD ((R43).piPerm i) []) ∧
      (∀ i < 24, 1 ∈ starMasks.getD i [] → i = 4 ∨ i = 11) ∧
      1 ∈ starMasks.getD 4 [] ∧ 1 ∈ starMasks.getD 11 [] ∧
      ((Finset.range 2048).filter fun c => QT.rowsXor (R43).col 11 c = c).card = 4 := by
  have hR := facts_of_chk row43
  rw [n43] at hR
  exact row_facts cols43 pi43 hR mask43 ce43

end CertificateChecks.KernelJ4Row

end
