module

public import Certificates.Kernel.J4TreeTop.Merge
public import Certificates.Kernel.J4TreeTop.Uneq
public import CFSG.Certificates.Kernel.J4TreeTop.Assembly
public import CFSG.Milestones.ASVolI.C31.J4NP.TreeInd
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.GH74.SmallRanks.AltM11
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Core
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
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Milestones.ASVolI.C31.J4NP.Is2A
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F918M7
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.SmithB51LnAut
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.Quasithin.Vol2.KGFactC31J4OffRun
public import CFSG.Quasithin.Vol2.KGFactC31Rad
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import Certificates.Kernel.J4Count.FixCE

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.J4TreeS CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] noncomputable def childOK (i j : Nat) : Bool :=
  (List.range 152).any (fun t => (mgRec t).i == i && (mgRec t).j == j) ||
    (List.range 16).any (fun t => (unRec t).i == i && (unRec t).j == j)

@[expose] def tgtOK (k : Nat) : Bool :=
  k == 0 || (Nat.ble 1 k && Nat.ble k treeN && !treeTopIds.contains k)

@[expose] noncomputable def kidsOK (i : Nat) (d : TopNode) : Bool :=
  (List.range d.children.length).all fun j =>
    childOK i j && tgtOK (d.children.getD j default).target

theorem topHq : Nat.beq (M QK QiK) oneK = true := by quickRfl

theorem child_rec {i j : Nat} (h : childOK i j = true) :
    (∃ c : TMerge, ∃ es, c.i = i ∧ c.j = j ∧ topMergeOK tabs (syRec i) c es = true) ∨
      (∃ c : TUneq, ∃ es, c.i = i ∧ c.j = j ∧ topUneqOK tabs (syRec i) c es = true) ∨
      (∃ c : TUneq, ∃ es, c.i = i ∧ c.j = j ∧ topPruneOK tabs (syRec i) c es = true) := by
  simp only [childOK, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  rcases h with ⟨t, ht, hi, hj⟩ | ⟨t, ht, hi, hj⟩
  · have hc : mgChk t = true := mg_all t ht
    unfold mgChk at hc
    rw [hi] at hc
    exact Or.inl ⟨mgRec t, mgEnts t, hi, hj, hc⟩
  · have hc : unChk t = true := un_all t ht
    unfold unChk at hc
    rw [hi] at hc
    split at hc
    · exact Or.inr (Or.inr ⟨unRec t, unEnts t, hi, hj, hc⟩)
    · exact Or.inr (Or.inl ⟨unRec t, unEnts t, hi, hj, hc⟩)

section Facts


theorem topTgt_of_tgtOK {k : ℕ} (h : tgtOK k = true) (h0 : k ≠ 0) : TopTgt k := by
  simp only [tgtOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Nat.ble_eq,
    Bool.not_eq_true'] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · exact absurd h h0
  have ht : k ∉ treeTopIds := fun hm => by
    have h4 : treeTopIds.contains k = true := List.elem_eq_true_of_mem hm
    exact Bool.false_ne_true (h3.symm.trans h4)
  have nf := burnsideJ4NP_nodeFacts h1 h2 ht
  refine ⟨nf.2.1, fun hc => ?_⟩
  have h2C : IsPGroup 2 ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep k : Set J)) :=
    IsPGroup.of_card (n := Nat.log2 (treeOrd k)) (by rw [hc]; exact nf.1)
  have hcl := burnsideJ4NP_isHCl_of_isPGroup h2C
  rwa [(nf.2.2 hc).1] at hcl


theorem top_facts {i : ℕ} (hi : i < 9) {d : TopNode} (hd : topNodes.getD i default = d)
    (hk : kidsOK i d = true)
    (hcov : TopCover (burnsideJ4NP_Rep d.node) (d.children.map fun c => burnsideJ4NP_treeElt c.y)) :
    burnsideJ4NP_Aff2A →
    Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep d.node : Set J)) = treeOrd d.node →
      burnsideJ4NP_TreeStep d.node ∧
        ∀ kd ∈ d.kids, Nat.card ↥(Hj ⊓ Subgroup.centralizer (burnsideJ4NP_Rep kd.1 : Set J)) =
          treeOrd kd.1 := by
  have hk' : ∀ j < d.children.length,
      childOK i j = true ∧ tgtOK (d.children.getD j default).target = true := by
    intro j hj
    have := List.all_eq_true.mp hk j (List.mem_range.mpr hj)
    simpa only [Bool.and_eq_true] using this
  have hg : topGlobOK tabs i (syRec i) = true := sy_all i hi
  exact fun haff => topNode_facts haff tabs_ok topHq hd hg (fun j hj => child_rec (hk' j hj).1)
    (fun j hj h0 => topTgt_of_tgtOK (hk' j hj).2 h0) hcov

end Facts

end CFSG.KC.J4TreeT
