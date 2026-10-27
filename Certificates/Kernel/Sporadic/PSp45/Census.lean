module

public import Certificates.Kernel.Sporadic.PSp45.Facts
public import Certificates.Kernel.Sporadic.PSp45.Inv
public import CFSG.Certificates.Kernel.SporSch.ChainKCover
public import CFSG.Certificates.Kernel.SporSch.MathieuOC2Sound
public import Certificates.Data.Seitz77Sec27SmallU42
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PSp45

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT
open CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.KGroups.Native CFSG.Monster.B.Co2

theorem c6129P_le_A : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  have hA : QA45.originalSubgroup = Subgroup.closure {g | g ∈ [tab x45, tab y45, tab f45]} := by
    rw [qa_eq, certificate_originalSubgroup]
  rw [qp_eq, certificate_originalSubgroup, Subgroup.closure_le, hA]
  intro g hg
  have hg' : g ∈ [tab x45, tab y45] := hg
  apply Subgroup.subset_closure
  change g ∈ [tab x45, tab y45, tab f45]
  rcases List.mem_cons.1 hg' with h | h
  · rw [h]
    exact List.mem_cons_self
  · rcases List.mem_cons.1 h with h | h
    · rw [h]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact absurd h List.not_mem_nil

theorem c6129cover : ∀ g ∈ QA45.originalSubgroup, orderOf g = 2 → ∃ i < 4,
    Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 45)))) =
      c6129CL.getD i 0 := by
  have hrep : ∀ i < c6129XL.length, repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR
      A45Q.TRI (c6129XL.getD i 0) (c6129CL.getD i 0) = true := by
    intro i hi
    have hi4 : i < 4 := hi
    interval_cases i
    · exact c6129rep0
    · exact c6129rep1
    · exact c6129rep2
    · exact c6129rep3
  have hdist : ∀ i < c6129XL.length, ∀ j < i, distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR
      A45Q.TR A45Q.TRI (c6129XL.getD j 0) (c6129XL.getD i 0) = true := by
    intro i hi j hj
    have hi4 : i < 4 := hi
    interval_cases i <;> interval_cases j
    · exact c6129d01
    · exact c6129d02
    · exact c6129d12
    · exact c6129d03
    · exact c6129d13
    · exact c6129d23
  have hord : ∀ i < c6129XL.length, ordC 45 6 (mask 6) (c6129XL.getD i 0) = 2 := by
    intro i hi
    have hi4 : i < 4 := hi
    interval_cases i
    · exact c6129ord0
    · exact c6129ord1
    · exact c6129ord2
    · exact c6129ord3
  have hsum : sumAllK (ordK A45Q.LR 4) c6129CL c6129XL.length =
      (cosetOrderTables (certificate (by decide) [tab x45, tab y45, tab f45] wordsA
        (#v[0, 1, 3, 9] : Vector (Fin 45) 4) (by decide)) 1 2).length := by
    rw [chainK_cosetCount (by decide) (by decide) chainA imgOne cOne (by norm_num) (by norm_num)
      (by decide) A45X.hc]
    exact c6129sum
  have h := chainK_cover chainA (by decide) (by decide) (by norm_num) (XL := c6129XL)
    (CL := c6129CL) rfl hrep hdist (mo := 2) (by norm_num) hord hsum
  rw [qa_eq]
  exact h

theorem c6129card0 : Nat.card ↥(QA45.originalSubgroup ⊓
    Subgroup.centralizer ({invReps.getD 0 1} : Set (Equiv.Perm (Fin 45)))) = 1152 := by
  rw [qa_eq]
  exact card_of_repK chainA (by decide) (by decide) (by norm_num) (prep_of_imageList imgRep0)
    c6129rep0

theorem c6129card1 : Nat.card ↥(QA45.originalSubgroup ⊓
    Subgroup.centralizer ({invReps.getD 1 1} : Set (Equiv.Perm (Fin 45)))) = 192 := by
  rw [qa_eq]
  exact card_of_repK chainA (by decide) (by decide) (by norm_num) (prep_of_imageList imgRep1)
    c6129rep1

theorem c6129inner {t : Equiv.Perm (Fin 45)} (ht : t ∈ QP45.originalSubgroup)
    (ho : orderOf t = 2) : ¬ 5 ∣ Nat.card ↥(QA45.originalSubgroup ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 45)))) := by
  have hn : (45 : ℕ) < 2 ^ 32 := by norm_num
  have hA : x45 ∈ QP45.originalSubgroup := gens_mem _ (by simp)
  have hB : y45 ∈ QP45.originalSubgroup := gens_mem _ (by simp)
  have hreps : ∀ r ∈ invReps, (1 : Equiv.Perm (Fin 45))⁻¹ * r ∈ QP45.originalSubgroup ∧
      orderOf r = 2 := by
    intro r hr
    have hmem : r ∈ QP45.originalSubgroup := by
      rw [invReps, List.mem_map] at hr
      obtain ⟨wd, -, rfl⟩ := hr
      exact evalCodes_mem _ gens_mem wd
    refine ⟨by simpa using hmem, ?_⟩
    have h3 := cover.2.2
    rw [List.all_eq_true] at h3
    exact (ordTest_iff perm_faithful (rep_toTable hn r) (by norm_num)).1
      (h3 _ (List.mem_map_of_mem hr))
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn QP45 validP.1 (pairTables_spec hn hA hB) 1
    (fun h hh => by simpa using hh) (by norm_num) invReps hreps 1000 cover.1
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov t (by simpa using ht) ho
  rw [card_centralizer_conj _ (c6129P_le_A hc)]
  have hr2 : r = invReps.getD 0 1 ∨ r = invReps.getD 1 1 := by
    simp only [invReps, invRepWords, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    simpa [invReps, invRepWords] using hr
  rcases hr2 with rfl | rfl
  · rw [c6129card0]
    norm_num
  · rw [c6129card1]
    norm_num

theorem c6129outer {t : Equiv.Perm (Fin 45)} (ht : t ∈ QA45.originalSubgroup)
    (ho : orderOf t = 2) (h5 : 5 ∣ Nat.card ↥(QA45.originalSubgroup ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 45))))) :
    2 ^ 5 ∣ Nat.card ↥(QA45.originalSubgroup ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 45)))) := by
  obtain ⟨i, hi, hc⟩ := c6129cover t ht ho
  rw [hc] at h5 ⊢
  interval_cases i <;> simp [c6129CL] at h5 ⊢

theorem c6129centLen (t : Equiv.Perm (Fin 45)) :
    centLenA 45 (enumA QA45) (toA t) = Nat.card ↥(QA45.originalSubgroup ⊓
      Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 45)))) := by
  rw [card_inf_centralizer QA45 validA.1 t, enumA_eq, centLenA, List.filter_map, List.length_map]
  congr 2
  funext g
  simp only [Function.comp_apply]
  exact eqA_eq_decide (rep_compA (rep_toA g) (rep_toA t)) (rep_compA (rep_toA t) (rep_toA g))

theorem c6129invol (t : Equiv.Perm (Fin 45)) : isInvolA 45 (toA t) = true ↔ orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isInvolA_rep (rep_toA t), orderOf_eq_prime_iff]
  simp

theorem c6129census : Certificates.Seitz77Sec27.u42CensusCheck = true := by
  unfold Certificates.Seitz77Sec27.u42CensusCheck Certificates.Seitz77Sec27.u42CensusCheckL
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro s hs
    rw [enumA_eq, List.mem_map] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    rw [mem_elemsT QP45 validP.1] at hg
    rw [c6129centLen]
    by_cases hI : isInvolA 45 (toA g) = true
    · have h := c6129inner hg ((c6129invol g).1 hI)
      rw [hI, Bool.not_true, Bool.false_or, Bool.not_eq_true', decide_eq_false_iff_not]
      exact h
    · rw [Bool.not_eq_true] at hI
      rw [hI, Bool.not_false, Bool.true_or]
  · intro s hs
    rw [enumA_eq, List.mem_map] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    rw [mem_elemsT QA45 validA.1] at hg
    rw [c6129centLen]
    by_cases hI : isInvolA 45 (toA g) = true
    · have ho := (c6129invol g).1 hI
      by_cases h5 : 5 ∣ Nat.card ↥(QA45.originalSubgroup ⊓
          Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 45))))
      · have h := c6129outer hg ho h5
        rw [hI, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr h
      · rw [hI, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not]
        exact Or.inl h5
    · rw [Bool.not_eq_true] at hI
      rw [hI, Bool.not_false, Bool.true_or, Bool.true_or]

end CertificateChecks.KernelSpor.PSp45

end
