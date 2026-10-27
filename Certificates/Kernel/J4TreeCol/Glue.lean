module

public import Certificates.Kernel.J4TreeCol.C7900
public import Certificates.Kernel.J4TreeCol.C7901
public import Certificates.Kernel.J4TreeCol.C7902
public import Certificates.Kernel.J4TreeCol.C7903
public import Certificates.Kernel.J4TreeCol.Q7900
public import Certificates.Kernel.J4TreeCol.Q7901
public import Certificates.Kernel.J4TreeCol.Q7902
public import Certificates.Kernel.J4TreeCol.Q7903
public import Certificates.Kernel.J4TreeCol.Cov
public import Certificates.Kernel.J4TreeNode.Facts
public import Certificates.Kernel.J4Q.QTBase
public import Certificates.Kernel.J4Q.C4025
public import CFSG.Certificates.Kernel.J4TreeCol.NodeSound
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictColIds
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.J4TreeNode.Glue
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

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4TreeN CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A CFSG.ASVolI

set_option maxRecDepth 400000

theorem prc_one_col : PRc 1 colMats.one := by
  obtain ⟨h1, h2⟩ := id_enc CertificateChecks.KernelJ4Q.hK
  exact ⟨_, h1, h2, by rw [map_one, rowsMatrix_idRows]⟩

theorem getN_out {d : ℕ} {l : List ℕ} {i : ℕ} (h : l.length ≤ i) : getN d l i = d := by
  rw [getN_eq_getD]
  exact List.getD_eq_default _ _ h

theorem g5_getL {m : ℕ} (hm : m < 3) : (g5Mats ())[m]? = (locMats ())[m]? := by
  unfold g5Mats
  have hl : (locMats ()).size = 3 := CertificateChecks.KernelJ4Q.matFacts.locSize
  exact Array.getElem?_append_left (by rw [hl]; exact hm)

theorem g5i_getL {m : ℕ} (hm : m < 3) : (g5Invs ())[m]? = (locInvs ())[m]? := by
  unfold g5Invs
  have hl : (locInvs ()).size = 3 := by
    have := CertificateChecks.KernelJ4Q.matFacts.locSize
    simpa [locInvs] using this
  exact Array.getElem?_append_left (by rw [hl]; exact hm)

theorem g5_getB (m : ℕ) : (g5Mats ())[m + 3]? = baseMats[m]? := by
  unfold g5Mats
  have hl : (locMats ()).size = 3 := CertificateChecks.KernelJ4Q.matFacts.locSize
  rw [Array.getElem?_append_right (by omega), hl, Nat.add_sub_cancel]

theorem g5i_getB (m : ℕ) : (g5Invs ())[m + 3]? = baseInvs[m]? := by
  unfold g5Invs
  have hl : (locInvs ()).size = 3 := by
    have := CertificateChecks.KernelJ4Q.matFacts.locSize
    simpa [locInvs] using this
  rw [Array.getElem?_append_right (by omega), hl, Nat.add_sub_cancel]

theorem gen5_out {k : ℕ} (hk : 5 ≤ k) : gen5 k = 1 := by
  unfold gen5
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem prc_g5 (k : ℕ) : PRc (gen5 k) (getN colMats.one colMats.g5 k) := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · have hX : Mx (gen5 k) = rowsMatrix ((g5Mats ())[k]?.getD idRows) :=
      (g5Mats_spec CertificateChecks.KernelJ4Q.matFacts k).symm
    refine ⟨_, ?_, ?_, hX⟩
    · by_cases h3 : k < 3
      · rw [g5_getL h3]
        exact (CertificateChecks.KernelJ4Q.loc_gens k).1
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        rw [g5_getB]
        exact (CertificateChecks.KernelJ4Q.base_gens m).1
    · by_cases h3 : k < 3
      · rw [g5_getL h3, (CertificateChecks.KernelJ4Q.loc_gens k).2]
        interval_cases k <;> rfl
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        rw [g5_getB, (CertificateChecks.KernelJ4Q.base_gens m).2]
        have : m < 2 := by omega
        interval_cases m <;> rfl
  · rw [gen5_out hk, getN_out (by exact hk)]
    exact prc_one_col

theorem prc_g5i (k : ℕ) : PRc (gen5 k)⁻¹ (getN colMats.one colMats.g5i k) := by
  rcases Nat.lt_or_ge k 5 with hk | hk
  · have hX : Mx (gen5 k)⁻¹ = rowsMatrix ((g5Invs ())[k]?.getD idRows) :=
      (g5Invs_spec CertificateChecks.KernelJ4Q.matFacts k).symm
    refine ⟨_, ?_, ?_, hX⟩
    · by_cases h3 : k < 3
      · rw [g5i_getL h3]
        exact (CertificateChecks.KernelJ4Q.loc_invs k).1
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        rw [g5i_getB]
        exact (CertificateChecks.KernelJ4Q.base_invs m).1
    · by_cases h3 : k < 3
      · rw [g5i_getL h3, (CertificateChecks.KernelJ4Q.loc_invs k).2]
        interval_cases k <;> rfl
      · obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
        rw [g5i_getB, (CertificateChecks.KernelJ4Q.base_invs m).2]
        have : m < 2 := by omega
        interval_cases m <;> rfl
  · rw [gen5_out hk, inv_one, getN_out (by exact hk)]
    exact prc_one_col

theorem prc_uJ {j : ℕ} (hj : j < 11) : PRc (uJ j) (getN colMats.one colMats.us j) := by
  have h := CertificateChecks.KernelJ4Q.uTab_enc j hj
  refine ⟨_, h.1, h.2.trans ?_, Mx_uJ CertificateChecks.KernelJ4Q.matFacts hj⟩
  interval_cases j <;> rfl

theorem kWords_length : kWords.length = 4 := rfl

theorem prc_kJ (i : ℕ) : PRc (kJ i) (getN colMats.one colMats.ks i) := by
  rcases Nat.lt_or_ge i 4 with hi | hi
  · have h := CertificateChecks.KernelJ4Q.kRows_enc hi
    rw [← CertificateChecks.KernelJ4Q.kTab_get hi] at h
    exact ⟨_, h.1, h.2, Mx_kJ CertificateChecks.KernelJ4Q.matFacts hi⟩
  · have e : kJ i = 1 := by
      unfold kJ
      rw [List.getD_eq_default _ _ (by rw [kWords_length]; exact hi)]
      rfl
    rw [e, getN_out (by exact hi)]
    exact prc_one_col

theorem colMats_ok : MatsOK colMats where
  consts := ⟨_, _, _, _, _, _, _, CertificateChecks.KernelJ4Q.hK⟩
  us_len := rfl
  us _ hj := prc_uJ hj
  ks_len := rfl
  ks := prc_kJ
  g5 := prc_g5
  g5i := prc_g5i

section Chunks


theorem chunk_sound {R : ℕ → CRec} {it : ℕ → List ℕ} {np nn : ℕ} {ids : List ℕ}
    (hn : ∀ j < nn, colNodeOK colMats tabs (R j) = true) (hc : covOK R it np nn = true)
    (hp : ∀ p < np,
      pairsOKP colMats (R ((it p).getD 0 0)) ((it p).getD 1 0) ((it p).getD 2 0) = true)
    (hids : ((List.range nn).map (fun j => (R j).k) == ids) = true) :
    ∀ k ∈ ids, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) := by
  intro k hk
  rw [← beq_iff_eq.1 hids] at hk
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hk
  have hj' := List.mem_range.1 hj
  exact colNode_sound colMats_ok tabs_ok sx_ok (hn j hj')
    (fun hm _ _ hab hb => pairs_sound hc hp hj' hm hab hb)

end Chunks

theorem ids7900 :
    ((List.range 442).map (fun j => (rec7900 j).k) == burnsideJ4NP_colIds0) = true := by
  quickRfl

theorem ids7901 :
    ((List.range 365).map (fun j => (rec7901 j).k) == burnsideJ4NP_colIds1) = true := by
  quickRfl

theorem ids7902 :
    ((List.range 261).map (fun j => (rec7902 j).k) == burnsideJ4NP_colIds2) = true := by
  quickRfl

theorem ids7903 :
    ((List.range 194).map (fun j => (rec7903 j).k) == burnsideJ4NP_colIds3) = true := by
  quickRfl

section Chunks


theorem c7900 : ∀ k ∈ burnsideJ4NP_colIds0, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) :=
  chunk_sound j4col7900_all j4colcov7900 j4colq7900_all ids7900

theorem c7901 : ∀ k ∈ burnsideJ4NP_colIds1, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) :=
  chunk_sound j4col7901_all j4colcov7901 j4colq7901_all ids7901

theorem c7902 : ∀ k ∈ burnsideJ4NP_colIds2, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) :=
  chunk_sound j4col7902_all j4colcov7902 j4colq7902_all ids7902

theorem c7903 : ∀ k ∈ burnsideJ4NP_colIds3, burnsideJ4NP_VerdictW (burnsideJ4NP_Wv k) :=
  chunk_sound j4col7903_all j4colcov7903 j4colq7903_all ids7903

end Chunks

end CFSG.KC.J4TreeCol

end
