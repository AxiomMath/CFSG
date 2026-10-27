
module

public import Certificates.Kernel.Sporadic.Fi22.C2068Base

public import Certificates.Kernel.Sporadic.Fi22.T2068
public import CFSG.Certificates.Kernel.Spor.LevelTrSound
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverBase1
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22LabA

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.Text
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22LabX

section Elements

theorem gen_val {s : Nat} (hs : s < 10) :
    ((fi22ExtGen s : fi22ExtS) : Equiv.Perm (Fin 3510)) = fi22ExtPerm (11 + s) := by
  rw [fi22ExtGen, dite_eq_left hs]
  rfl

theorem rep_line {L : Nat} (hL : L < 185) : Rep 3510 (unpack 3510 12 (Lx L)) (fi22ExtPerm L) ∧
    Rep 3510 (unpack 3510 12 (LI L)) (fi22ExtPerm L)⁻¹ := by
  have h := rep_fi22ExtPerm hL
  rw [Fi22E2067.ext_eq hL] at h
  exact ⟨h, rep_inv_of_isInvA h (invEqK_sound (Fi22E2067.perm3510 hL)).2⟩

theorem lx_lt {L x : Nat} (hL : L < 185) (hx : x < 3510) : pg 12 (mask 12) (Lx L) x < 3510 := by
  rw [← unpack_get' (w := 12) hx]
  exact (rep_line hL).1.lt hx

theorem li_lt {L x : Nat} (hL : L < 185) (hx : x < 3510) : pg 12 (mask 12) (LI L) x < 3510 := by
  rw [← unpack_get' (w := 12) hx]
  exact (rep_line hL).2.lt hx

theorem elt_apply {I p : Nat} (_hI : I < 262144) (hp : p < 3510) :
    ((fi22ExtEltIdx I ⟨p, hp⟩ : Fin 3510) : Nat) = XI I p := by
  rw [fi22ExtEltIdx_apply I ⟨p, hp⟩]
  have hv : (if (I % 2 == 1) then fi22ExtVArr[p]! else p) =
      nIf(Nat.beq (Nat.mod I 2) 1, pg 12 (mask 12) (Lx 1) p, p) := by
    rcases Nat.mod_two_eq_zero_or_one I with h | h
    · have hb : (I % 2 == 1) = false := by rw [h]; rfl
      rw [ite_eq_right (by rw [hb]; exact Bool.false_ne_true), show Nat.mod I 2 = 0 from h]
      rfl
    · have hb : (I % 2 == 1) = true := by rw [h]; rfl
      rw [ite_eq_left hb, show Nat.mod I 2 = 1 from h, fi22ExtVArr,
        Fi22E2067.ext_eq (L := 1) (by norm_num),
        unpack_get' hp]
      rfl
  have hvl : nIf(Nat.beq (Nat.mod I 2) 1, pg 12 (mask 12) (Lx 1) p, p) < 3510 := by
    cases Nat.beq (Nat.mod I 2) 1
    · exact hp
    · exact lx_lt (by norm_num) hp
  rw [hv, qi_eq, unpack_get' hvl]
  have hq := li_lt (L := 0) (by norm_num) hvl
  have ha : (fi22ExtCoord I).1.val < 1024 := (fi22ExtCoord I).1.2
  have hb : (fi22ExtCoord I).2.1.val < 32 := (fi22ExtCoord I).2.1.2
  have hc : (fi22ExtCoord I).2.2.val < 4 := (fi22ExtCoord I).2.2.2
  rw [tr3_eq ha hb hc hq]
  have ht : tr 0 (fi22ExtCoord I).1.val (tr 1024 (fi22ExtCoord I).2.1.val
      (tr 1056 (fi22ExtCoord I).2.2.val (pg 12 (mask 12) (LI 0)
        (nIf(Nat.beq (Nat.mod I 2) 1, pg 12 (mask 12) (Lx 1) p, p))))) < 3510 :=
    tr_lt (by rw [Nat.add_eq]; omega) (tr_lt (by rw [Nat.add_eq]; omega)
      (tr_lt (by rw [Nat.add_eq]; omega) hq))
  rw [fi22ExtQArr, Fi22E2067.ext_eq (L := 0) (by norm_num), unpack_get' ht, XI, strictN_eq']
  rfl

theorem dp_val {t : Nat} (ht : t < 6) : (Dp t ht : Nat) = Db t := by
  have hb : bs t < 256 := by interval_cases t <;> decide
  rw [Dp, ← fi22ExtDArr_get, Fi22X.dArr_get hb]
  rfl

theorem db_lt {t : Nat} (ht : t < 6) : Db t < 3510 := by
  rw [← dp_val ht]
  exact Fin.isLt _

theorem sepS {x y : fi22ExtS}
    (h : ∀ t (ht : t < 6), (((x : Equiv.Perm (Fin 3510)) (Dp t ht) : Fin 3510) : Nat) =
      ((y : Equiv.Perm (Fin 3510)) (Dp t ht) : Nat)) : x = y := by
  have hfix : ∀ t (ht : t < 6), fi22ExtRes (x⁻¹ * y) ⟨bs t, by interval_cases t <;> decide⟩ =
      ⟨bs t, by interval_cases t <;> decide⟩ := by
    intro t ht
    apply fi22ExtDeltaPt_injective
    rw [fi22ExtRes_apply]
    change (x : Equiv.Perm (Fin 3510))⁻¹ ((y : Equiv.Perm (Fin 3510)) (Dp t ht)) = Dp t ht
    rw [Equiv.Perm.inv_eq_iff_eq]
    exact (Fin.ext (h t ht)).symm
  have hmem : fi22ExtRes (x⁻¹ * y) ∈ fi22ExtSmallChain.originalSubgroup := by
    rw [← fi22ExtRes_range]
    exact ⟨_, rfl⟩
  have h1 : fi22ExtRes (x⁻¹ * y) = 1 := by
    refine fi22ExtSmallChain.eq_one_of_fixes_base fi22ExtSmallChain_valid hmem fun i => ?_
    have hc : fi22ExtSmallChain.baseCount = 6 := fi22ExtSmallChain_arrays.base_size.symm
    have hv := fi22ExtSmallChain_arrays.base_val i
    obtain ⟨i, hi⟩ := i
    have hi' : i < 6 := hc ▸ hi
    have hb : (#[0, 1, 2, 3, 4, 6] : Array Nat)[i]! = bs i := by
      interval_cases i <;> rfl
    have hg : fi22ExtSmallChain.base.get ⟨i, hi⟩ = ⟨bs i, by interval_cases i <;> decide⟩ :=
      Fin.ext (hv.trans hb)
    rw [hg]
    exact hfix i hi'
  have h2 : x⁻¹ * y = 1 := fi22ExtRes_injective (h1.trans (map_one _).symm)
  exact (inv_mul_eq_one.1 h2)

theorem elt_apply' {I : Nat} (hI : I < 262144) (x : Fin 3510) :
    ((fi22ExtEltIdx I x : Fin 3510) : Nat) = XI I x.val := by
  obtain ⟨p, hp⟩ := x
  exact elt_apply hI hp

theorem conj_eq {s I J : Nat}
    (hs : s < 10) (hI : I < 262144) (hJ : J < 262144) (h : conjB s I J = true) :
    fi22ExtE I = fi22ExtGen s * fi22ExtE J * (fi22ExtGen s)⁻¹ := by
  refine sepS fun t ht => ?_
  have hr := rep_line (L := 11 + s) (by omega)
  have e := Nat.eq_of_beq_eq_true (allN_spec h t ht)
  have key : ((fi22ExtGen s * fi22ExtE J * (fi22ExtGen s)⁻¹ : fi22ExtS) : Equiv.Perm (Fin 3510))
      (Dp t ht) = fi22ExtPerm (11 + s) (fi22ExtEltIdx J ((fi22ExtPerm (11 + s))⁻¹ (Dp t ht))) := by
    rw [conj_apply, gen_val hs, fi22ExtE_val]
  rw [key, fi22ExtE_val, elt_apply' hI, perm_val hr.1, elt_apply' hJ, perm_val hr.2, dp_val ht]
  exact e

theorem res_rep {I : Nat} (hI : I < 262144) :
    Rep 256 (fi22ExtResArr I) (fi22ExtRes (fi22ExtE I)) := rep_fi22ExtResArr hI

theorem conj_ok {s I J : Nat}
    (hs : s < 10) (hI : I < 262144) (hJ : J < 262144) (h : conjB s I J = true) :
    eqA 256 (fi22ExtResArr I)
      (conjArr 256 fi22ExtSteps[s]! fi22ExtStepsInv[s]! (fi22ExtResArr J)) = true := by
  have hst := rep_fi22ExtSteps (k := s) (by rw [steps_size]; exact hs)
  refine (eqA_iff (res_rep hI) (rep_compA hst.1 (rep_compA (res_rep hJ) hst.2))).2 ?_
  rw [conj_eq hs hI hJ h, map_mul, map_mul, map_inv, mul_assoc]

theorem isInv_true {I : Nat}
    (hI : I < 262144) (h : isInvK I = true) : isInvArr 256 (fi22ExtResArr I) = true := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have hsq : fi22ExtE I * fi22ExtE I = 1 := sepS fun t ht => by
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, OneMemClass.coe_one, Equiv.Perm.one_apply,
      fi22ExtE_val, elt_apply' hI, elt_apply' hI, dp_val ht]
    exact Nat.eq_of_beq_eq_true (allN_spec h2 t ht)
  have hne : fi22ExtE I ≠ 1 := by
    intro h1'
    obtain ⟨t, ht, hne⟩ := not_allN h1
    apply hne
    have hx : (((fi22ExtE I : Equiv.Perm (Fin 3510)) (Dp t ht) : Fin 3510) : Nat) =
        ((Dp t ht : Fin 3510) : Nat) := by
      rw [h1', OneMemClass.coe_one, Equiv.Perm.one_apply]
    rw [fi22ExtE_val, elt_apply' hI, dp_val ht] at hx
    change Nat.beq (XI I (Db t)) (Db t) = true
    rw [hx]
    exact Nat.beq_refl _
  unfold isInvArr
  rw [Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨?_, (eqA_iff (rep_compA (res_rep hI) (res_rep hI)) rep_idA).2
    (by rw [← map_mul, hsq, map_one])⟩
  cases e : eqA 256 (fi22ExtResArr I) (idA 256)
  · rfl
  · exact absurd (fi22ExtRes_injective (((eqA_iff (res_rep hI) rep_idA).1 e).trans
      (map_one _).symm)) hne

theorem isInv_false {I : Nat}
    (hI : I < 262144) (h : isInvK I = false) : isInvArr 256 (fi22ExtResArr I) = false := by
  unfold isInvK at h
  cases e1 : allN 6 (fun t => Nat.beq (XI I (Db t)) (Db t))
  · rw [e1] at h
    have e2 : allN 6 (fun t => Nat.beq (XI I (XI I (Db t))) (Db t)) = false := by
      simpa only [Bool.not_false] using h
    unfold isInvArr
    cases e3 : eqA 256 (compA 256 (fi22ExtResArr I) (fi22ExtResArr I)) (idA 256)
    · rw [Bool.and_false]
    · exfalso
      have he := (eqA_iff (rep_compA (res_rep hI) (res_rep hI)) rep_idA).1 e3
      rw [← map_mul] at he
      have hsq : fi22ExtE I * fi22ExtE I = 1 := fi22ExtRes_injective (he.trans (map_one _).symm)
      have hall : allN 6 (fun t => Nat.beq (XI I (XI I (Db t))) (Db t)) = true := by
        refine allN_of_forall fun t ht => ?_
        have hx : (((fi22ExtE I * fi22ExtE I : fi22ExtS) : Equiv.Perm (Fin 3510)) (Dp t ht) :
            Nat) = ((Dp t ht : Fin 3510) : Nat) := by
          rw [hsq, OneMemClass.coe_one, Equiv.Perm.one_apply]
        rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, fi22ExtE_val, elt_apply' hI, elt_apply' hI,
          dp_val ht] at hx
        change Nat.beq (XI I (XI I (Db t))) (Db t) = true
        rw [hx]
        exact Nat.beq_refl _
      rw [hall] at e2
      exact Bool.noConfusion e2
  · have h1 : fi22ExtE I = 1 := sepS fun t ht => by
      rw [OneMemClass.coe_one, Equiv.Perm.one_apply, fi22ExtE_val, elt_apply' hI, dp_val ht]
      exact Nat.eq_of_beq_eq_true (allN_spec e1 t ht)
    unfold isInvArr
    have e : eqA 256 (fi22ExtResArr I) (idA 256) = true :=
      (eqA_iff (res_rep hI) rep_idA).2 (by rw [h1, map_one])
    rw [e]
    rfl

theorem labelOK_rec :
    labelOKRes 256 262144 fi22TLevels fi22ExtQArr fi22ExtQiArr fi22ExtVArr fi22ExtDArr
      fi22ExtPosArr fi22ExtSteps fi22ExtStepsInv fi22ExtRootsRec fi22ExtLabelsRec 4 = true := by
  unfold labelOKRes labelOK
  refine parLt_of_forall fun I hI => ?_
  change labelOKAt 256 262144 fi22ExtResArr fi22ExtSteps fi22ExtStepsInv fi22ExtRootsRec
    fi22ExtLabelsRec I = true
  unfold labelOKAt
  dsimp only
  rw [roots_size, lab_get hI, steps_size]
  cases hk : isInvK I
  · rw [isInv_false hI hk, ite_eq_right Bool.false_ne_true, labOf_noinv (row_noinv hI hk)]
    rfl
  · obtain ⟨hp, -, hl, hroot, hpar, hnb⟩ := row_inv hI hk
    rw [isInv_true hI hk, ite_eq_left rfl, labOf_inv hp, dep_get hI, depOf_inv hp]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨hl, ?_⟩, allLt_iff.2 fun s hs => ?_⟩
    · by_cases hd : DE (PP I) = 0
      · rw [ite_eq_left (by rw [hd]; rfl), beq_iff_eq, (root_parts hl).1]
        exact hroot hd
      · obtain ⟨hJ, hdep, hlab, hs, hc⟩ := hpar hd
        rw [ite_eq_right (by simp [hd]), par_get hI hp, gen_get hI hp]
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        rw [dep_get hJ, lab_get hJ]
        exact ⟨⟨⟨⟨hJ, hdep⟩, hlab⟩, hs⟩, conj_ok hs hI hJ hc⟩
    · obtain ⟨hJ, hlab, hc⟩ := hnb s hs
      rw [nb_get hI hs hp]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rw [lab_get hJ]
      exact ⟨⟨hJ, hlab⟩, conj_ok hs hJ hI hc⟩

theorem full_ok {j : Nat}
    (hj : j < 79) :
    eqA 3510 (fi22ExtFullArr fi22ExtRootsRec[j]!) (fi22ExtArr (27 + j)) = true := by
  obtain ⟨e1, hr, -, hx⟩ := root_parts hj
  rw [e1, Fi22E2067.ext_eq (by omega)]
  refine eqA_of_get fun p hp => ?_
  rw [(rep_fi22ExtFullArr hr).apply hp, elt_apply hr hp, hx p hp, unpack_get' hp]
  rfl

theorem facts :
    labelOKRes 256 262144 fi22TLevels fi22ExtQArr fi22ExtQiArr fi22ExtVArr fi22ExtDArr
      fi22ExtPosArr fi22ExtSteps fi22ExtStepsInv fi22ExtRootsRec fi22ExtLabelsRec 4 = true ∧
    (∀ j < 79, fi22ExtRootsRec[j]! < 262144 ∧ fi22ExtLabelsRec.lab[fi22ExtRootsRec[j]!]! = j) ∧
    (∀ j < 79, labCount fi22ExtLabelsRec.lab 262144 j = fi22ExtClassSizes.getD j 0) ∧
    (∀ j < 79, eqA 3510 (fi22ExtFullArr fi22ExtRootsRec[j]!) (fi22ExtArr (27 + j)) = true) ∧
    (∀ k < 10, isInvA 256 fi22ExtSteps[k]! fi22ExtStepsInv[k]! = true) ∧
    (∀ j < 79, fi22InP (fi22ExtArr (106 + j)) = true ∧
      eqA 3510 (compA 3510 (fi22ExtArr (106 + j)) (fi22ExtArr (27 + j)))
        (compA 3510 (fi22ExtArr (21 + fi22ExtGlobalClasses.getD j 0)) (fi22ExtArr (106 + j))) =
        true) ∧
    (∀ i < 3, eqA 3510 (fi22ExtArr (21 + i)) (fi22OuterStrong3510 6)[i]! = true) ∧
    eqA 3510 (fi22ExtArr 24) fi22GraphOuterArr = true ∧
    (∀ k < 6, isInvArr 3510 (fi22ExtArr (21 + k)) = true) ∧
    ((List.range 6).map fun k => fixCount 3510 (fi22ExtArr (21 + k))) =
      [54, 182, 694, 72, 360, 64] ∧
    (∀ k < 3, fi22InP (fi22ExtArr (21 + k)) = true) ∧
    (∀ k < 3, fi22InP (fi22ExtArr (24 + k)) = false ∧
      fi22InP (compA 3510 fi22GraphOuterArr (fi22ExtArr (24 + k))) = true) ∧
    labelledCount fi22ExtLabelsRec.lab 262144 79 = 6143 := by
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := outer_ok
  refine ⟨labelOK_rec, fun j hj => ?_, fun j hj => labCount_ok hj, fun j hj => full_ok hj,
    fun k hk => steps_ok hk, fun j hj => h_ok hj, o1, o2, o3, o4, o5, o6, labelled_ok⟩
  obtain ⟨e1, hr, hl, -⟩ := root_parts hj
  rw [e1, lab_get hr]
  exact ⟨hr, hl⟩

end Elements

end CertificateChecks.KernelSpor.Fi22LabA

end
