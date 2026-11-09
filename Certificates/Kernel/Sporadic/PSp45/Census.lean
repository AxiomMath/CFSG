module

public import Certificates.Kernel.Sporadic.PSp45.Facts
public import Certificates.Kernel.Sporadic.PSp45.Inv
public import Certificates.Kernel.Sporadic.PSp45.A45BT
public import CFSG.Certificates.Kernel.SporSch.MathieuBTSound
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

theorem a45Tot2 : Nat.beq (sumOrdK 45 6 (mask 6) (ordK A45Q.LR 4) A45B.XL A45B.CL 2
    A45B.XL.length) 891 = true := by quickRfl

theorem a45ClassEq : ClassEqK 45 6 A45Q.LR A45Q.TR A45Q.TRI A45Q.BP 4 A45B.XL A45B.CL :=
  ⟨rfl, A45B.hr, A45B.hd, A45B.hs⟩

theorem c6129XL_get0 : c6129XL.getD 0 0 = c6129X0 := by
  unfold c6129XL
  exact List.getD_cons_zero

theorem c6129XL_get1 : c6129XL.getD 1 0 = c6129X1 := by
  unfold c6129XL
  exact List.getD_cons_succ.trans List.getD_cons_zero

theorem c6129cover : ∀ g ∈ QA45.originalSubgroup, orderOf g = 2 → ∃ i < 4,
    Nat.card ↥(QA45.originalSubgroup ⊓ Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin 45)))) =
      c6129CL.getD i 0 := by
  have hrep : ∀ i < c6129XL.length, repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR
      A45Q.TRI (c6129XL.getD i 0) (c6129CL.getD i 0) = true := by
    intro i hi
    have hi4 : i < 4 := hi
    interval_cases i
    · rw [c6129XL_get0]
      exact c6129rep0
    · rw [c6129XL_get1]
      exact c6129rep1
    · exact c6129rep2
    · exact c6129rep3
  have hdist : ∀ i < c6129XL.length, ∀ j < i, distK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR
      A45Q.TR A45Q.TRI (c6129XL.getD j 0) (c6129XL.getD i 0) = true := by
    intro i hi j hj
    have hi4 : i < 4 := hi
    interval_cases i <;> interval_cases j
    · rw [c6129XL_get0, c6129XL_get1]
      exact c6129d01
    · rw [c6129XL_get0]
      exact c6129d02
    · rw [c6129XL_get1]
      exact c6129d12
    · rw [c6129XL_get0]
      exact c6129d03
    · rw [c6129XL_get1]
      exact c6129d13
    · exact c6129d23
  have hord : ∀ i < c6129XL.length, ordC 45 6 (mask 6) (c6129XL.getD i 0) = 2 := by
    intro i hi
    have hi4 : i < 4 := hi
    interval_cases i
    · rw [c6129XL_get0]
      exact c6129ord0
    · rw [c6129XL_get1]
      exact c6129ord1
    · exact c6129ord2
    · exact c6129ord3
  have hsum : sumAllK (ordK A45Q.LR 4) c6129CL c6129XL.length =
      (cosetOrderTables (certificate (by decide) [tab x45, tab y45, tab f45] wordsA
        (#v[0, 1, 3, 9] : Vector (Fin 45) 4) (by decide)) 1 2).length := by
    rw [(classEq_sound (by decide) (by decide) chainA a45ClassEq (mo := 2) (by norm_num)
      (by norm_num)).2, Nat.eq_of_beq_eq_true a45Tot2]
    exact c6129sum
  have h := chainK_cover chainA (by decide) (by decide) (by norm_num) (XL := c6129XL)
    (CL := c6129CL) rfl hrep hdist (mo := 2) (by norm_num) hord hsum
  rw [qa_eq]
  exact h

theorem c6129card_conj {V U : List Int} {R C : Nat} {r : Equiv.Perm (Fin 45)}
    (hr : imageList r = (unpack 45 6 R).toList) (hV : abOK V = true) (hU : abOK U = true)
    (hc : Nat.beq (pcomp 45 6 (mask 6) (c6129A V) R) (pcomp 45 6 (mask 6) (c6129A U) (c6129A V)) =
      true)
    (h : repK 45 6 (mask 6) (45 * 6) A45Q.BP 4 A45Q.LR A45Q.TR A45Q.TRI (c6129A U) C = true) :
    Nat.card ↥(QA45.originalSubgroup ⊓
      Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 45)))) = C := by
  have hn : (45 : ℕ) < 2 ^ 32 := by norm_num
  have pV := prep_of_imageList (img_word hV (Nat.beq_refl (c6129A V)))
  have pU := prep_of_imageList (img_word hU (Nat.beq_refl (c6129A U)))
  have hvr : evalCodes [x45, y45] V * r = evalCodes [x45, y45] U * evalCodes [x45, y45] V := by
    have e : imageList (evalCodes [x45, y45] V * r) =
        imageList (evalCodes [x45, y45] U * evalCodes [x45, y45] V) := by
      rw [imageList_of_prep (Raw.Orb.prep_pcomp hn pV (prep_of_imageList hr)),
        imageList_of_prep (Raw.Orb.prep_pcomp hn pU pV), Nat.eq_of_beq_eq_true hc]
    exact Equiv.ext fun x => Fin.ext (congrFun (List.ofFn_injective e) x)
  have hu : evalCodes [x45, y45] U = evalCodes [x45, y45] V * r * (evalCodes [x45, y45] V)⁻¹ := by
    rw [hvr, mul_inv_cancel_right]
  rw [← card_centralizer_conj _ (c6129P_le_A (evalCodes_mem _ gens_mem V)) r, ← hu, qa_eq]
  exact card_of_repK chainA (by decide) (by decide) (by norm_num) pU h

theorem c6129card0 : Nat.card ↥(QA45.originalSubgroup ⊓
    Subgroup.centralizer ({invReps.getD 0 1} : Set (Equiv.Perm (Fin 45)))) = 1152 :=
  c6129card_conj imgRep0 c6129ab.1 c6129ab.2.2.1 c6129cj0 c6129rep0

theorem c6129card1 : Nat.card ↥(QA45.originalSubgroup ⊓
    Subgroup.centralizer ({invReps.getD 1 1} : Set (Equiv.Perm (Fin 45)))) = 192 :=
  c6129card_conj imgRep1 c6129ab.2.1 c6129ab.2.2.2 c6129cj1 c6129rep1

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
