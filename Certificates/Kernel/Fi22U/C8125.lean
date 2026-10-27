
module

public import Certificates.Kernel.Fi22U.M8125K
public import Certificates.Kernel.Fi22U.C8126
public import Certificates.Kernel.Sporadic.Fi22.C3150
public import CFSG.RankThree.Native.Fi22UCentralizerBase
public import CFSG.Certificates.Kernel.Fi22U.WordSound
import CFSG.Certificates.Kernel.Spor.RawSiftK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22U.C8125

open CFSG.Monster.B.Fischer CFSG.RankThree.Native.Fi22U CFSG.KC.Fi22U CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CertificateChecks.KernelSpor CertificateChecks.KernelFi22U Quiver.SchreierGraph

theorem sizeU : (fi22OuterStrong693 2).size = 49 := by
  simp [fi22OuterStrong693, fi22OuterLines693]

theorem hdU : Orb.Hd 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45] 46
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 46 49 fi22OuterUnitaryDerivations) :=
  Orb.hd_of_head (by rw [sizeU]; omega) (rawHeadK_sound C8126.binds Fi22UO.head)

theorem genU_le : Orb.Gen 693 (fi22OuterStrong693 2) 46 ≤ fi22OuterX := by
  rw [Orb.Gen, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  rw [fi22OuterX, RawSchreierDatum.originalSubgroup]
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, fi22OuterChainUnitary, RawSchreierDatum.mem_ofArrays_original]
  exact ⟨j, j.2, rfl⟩

@[expose] noncomputable def wU (k : Nat) : List Nat := [W693.w0, W693.w1, W693.w2].getD k []

theorem wordU {k : Nat} (hk : k < 3) : CFSG.KS.Prim.wordEqK 693 10 (mask 10) (pidn 693 10)
    Fi22UO.S Fi22UO.SI 49 (wOf (wU k)) (Fi22O693T.L (64 + k)) = true := by
  interval_cases k
  exacts [MK.u0, MK.u1, MK.u2]

theorem seed_mem_X {k : Nat} (hk : k < 3) : fi22OuterPerm693 (64 + k) ∈ fi22OuterX :=
  genU_le (mem_Gen_of_wordEqK hdU ⟨sizeU, C8126.binds.2.2.2.2.1⟩ C8126.perms (wordU hk)
    (Fi22F1O.arr693_eq (by omega)) (rep_fi22OuterPerm693 (by omega))).2

theorem sift3 : ∀ k < 3, siftA 693 (rawLevels 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45])
    #[0, 1, 3, 9, 45] 0 (fi22OuterArr693 (64 + k)) = true := fun k hk =>
  (siftA_iff_mem_originalSubgroup fi22OuterChainUnitary_arrays (by norm_num) fi22U_chainOK
    (rep_fi22OuterPerm693 (L := 64 + k) (by omega))).2 (seed_mem_X hk)

theorem bindsM : Binds 693 10 Fi22MO.S 15 5 Fi22MO.BP (fi22OuterStrong693 3) #[0, 1, 3, 9, 45] := by
  refine ⟨by norm_num, by norm_num, by norm_num, by simp [fi22OuterStrong693, fi22OuterLines693],
    fun j hj => ?_, rfl, fun t ht => Nat.eq_of_beq_eq_true (allN_spec MK.bOK t ht)⟩
  rw [fi22OuterStrong693_three_get hj, Fi22F1O.arr693_eq (by omega),
    Nat.eq_of_beq_eq_true (allN_spec MK.sOK j hj)]

theorem orbitsM : rawOrbitSizes 693 (fi22OuterStrong693 3) #[0, 1, 3, 9, 45] =
    [693, 512, 120, 36, 6] := by
  have h := rawOrbitSizesK_orb (NS := 11) (CH := 64) (LR := Fi22MO.LR) (PSI := Fi22MO.SI) bindsM
    (Orb.head_facts Fi22MO.head).1 Fi22MO.ho (by norm_num)
  have e : (List.range 5).map (fun i => rcnt (Fi22MO.LR i)) = [693, 512, 120, 36, 6] := by
    decide +kernel
  exact h.trans e

theorem chainM : rawChainOK 693 ((fi22OuterStrong693 3).extract 0 fi22OuterM693GenCount)
    (fi22OuterStrong693 3) #[0, 1, 3, 9, 45]
    (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations) 4 = true := by
  change rawChainOK 693 ((fi22OuterStrong693 3).extract 0 3) (fi22OuterStrong693 3)
    #[0, 1, 3, 9, 45] (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 15
      fi22OuterM693Derivations) 4 = true
  refine rawChainK_of_card_orb 4 bindsM Fi22MO.head Fi22MO.ho (by norm_num : 693 ≤ 11 * 64) ?_
  rw [orbitsM]
  have hle : Subgroup.closure (Set.range fun j : Fin 3 =>
      permOfArr 693 (fi22OuterStrong693 3)[j.val]!) ≤ fi22OuterX := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    change permOfArr 693 (fi22OuterStrong693 3)[(j : ℕ)]! ∈ fi22OuterX
    rw [fi22OuterStrong693_three_get (by omega)]
    exact seed_mem_X j.2
  exact (Subgroup.card_le_of_le hle).trans (by rw [card_fi22OuterX]; norm_num)

theorem mp_eq : fi22OuterMPointsNat =
    (List.range 693).map fun i => pg 12 (mask 12) (Fi22OMP.F 0) i := by
  unfold fi22OuterMPointsNat hex3List
  refine List.map_congr_left fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have e : (hexTable3 693 0 fi22OuterMPointsHex)[i]! =
      CFSG.Monster.B.Max2.Native.hexAt fi22OuterMPointsHex.toUTF8 (3 * i) 3 := by
    simp [hexTable3, hi']
  rw [← e, Fi22F1O.mTab, Orb.unpack_get hi']

theorem mp_get {i : Nat} (hi : i < 693) :
    fi22OuterMPointsNat.getD i 0 = pg 12 (mask 12) (Fi22OMP.F 0) i := by
  rw [mp_eq, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem mp_lt {i : Nat} (hi : i < 693) : pg 12 (mask 12) (Fi22OMP.F 0) i < 3510 :=
  Nat.blt_eq.mp (allN_spec Fi22F1O.mLt i hi)

theorem nodup : fi22OuterMPointsNat.Nodup := by
  rw [mp_eq]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro a ha b hb e
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := allN_spec (allN_spec MK.distinct b hb') a h
    rw [e, Nat.beq_refl] at this
    exact Bool.false_ne_true this
  · have := allN_spec (allN_spec MK.distinct a ha') b h
    rw [e, Nat.beq_refl] at this
    exact Bool.false_ne_true this

theorem cuinv {y : Nat} (hy : y < 693) :
    (invCand 693 (fi22OuterArr693 0))[y]! = pg 10 (mask 10) Inv693.inv0 y := by
  have r0 := rep_fi22OuterPerm693 (L := 0) (by norm_num)
  have ri := rep_invCand r0
  rw [ri ⟨y, hy⟩]
  set i := (fi22OuterPerm693 0)⁻¹ ⟨y, hy⟩ with hi
  have e : pg 10 (mask 10) (Fi22O693T.L 0) i = y := by
    rw [← Orb.unpack_get i.2, ← Fi22F1O.arr693_eq (by norm_num), r0 i, hi]
    simp
  have hinv := Nat.eq_of_beq_eq_true (allN_spec MK.inv i i.2)
  rw [e] at hinv
  exact hinv.symm

theorem restrict : ∀ k < 3, ∀ j < 693,
    fi22OuterMPointsNat.getD ((invCand 693 (fi22OuterArr693 0))[
      (fi22OuterArr693 (64 + k))[(fi22OuterArr693 0)[j]!]!]!) 0 =
    (fi22OuterArr3510 (3 + k))[fi22OuterMPointsNat.getD j 0]! := by
  intro k hk j hj
  have r0 := rep_fi22OuterPerm693 (L := 0) (by norm_num)
  have rk := rep_fi22OuterPerm693 (L := 64 + k) (by omega)
  have a0 : (fi22OuterArr693 0)[j]! = pg 10 (mask 10) (Fi22O693T.L 0) j := by
    rw [Fi22F1O.arr693_eq (by norm_num), Orb.unpack_get hj]
  have hx : pg 10 (mask 10) (Fi22O693T.L 0) j < 693 := by
    rw [← a0]
    exact r0.lt hj
  have a1 : (fi22OuterArr693 (64 + k))[pg 10 (mask 10) (Fi22O693T.L 0) j]! =
      pg 10 (mask 10) (Fi22O693T.L (64 + k)) (pg 10 (mask 10) (Fi22O693T.L 0) j) := by
    rw [Fi22F1O.arr693_eq (by omega), Orb.unpack_get hx]
  have hy : pg 10 (mask 10) (Fi22O693T.L (64 + k)) (pg 10 (mask 10) (Fi22O693T.L 0) j) < 693 := by
    rw [← a1]
    exact rk.lt hx
  have hz : pg 10 (mask 10) Inv693.inv0
      (pg 10 (mask 10) (Fi22O693T.L (64 + k)) (pg 10 (mask 10) (Fi22O693T.L 0) j)) < 693 := by
    rw [← cuinv hy]
    exact (rep_invCand r0).lt hy
  rw [a0, a1, cuinv hy, mp_get hz, mp_get hj, Fi22F1O.arr3510_eq (by omega),
    Orb.unpack_get (mp_lt hj)]
  exact Nat.eq_of_beq_eq_true (allN_spec (MK.restrict k hk) j hj)

theorem zfix : ∀ j < 693, (fi22OuterArr3510 1)[fi22OuterMPointsNat.getD j 0]! =
    fi22OuterMPointsNat.getD j 0 := by
  intro j hj
  rw [mp_get hj, Fi22F1O.arr3510_eq (by norm_num), Orb.unpack_get (mp_lt hj)]
  exact Nat.eq_of_beq_eq_true (allN_spec MK.fix j hj)

theorem sizeM : (fi22OuterStrong3510 3).size = 17 := Fi22C3150.sizeM

theorem genM_le : Orb.Gen 3510 (fi22OuterStrong3510 3) 3 ≤ fi22OuterM := by
  rw [Orb.Gen, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  change permOfArr 3510 (fi22OuterStrong3510 3)[(j : ℕ)]! ∈ fi22OuterM
  rw [fi22OuterStrong3510_three_get (by omega)]
  exact mem_fi22OuterM_gen j.2

@[expose] noncomputable def wM (i : Nat) : List Nat :=
  [W3510.w0, W3510.w1, W3510.w2, W3510.w3].getD i []

theorem wordM {i : Nat} (hi : i < 4) : CFSG.KS.Prim.wordEqK 3510 12 (mask 12) (pidn 3510 12)
    Fi22MR.S Fi22MR.SI 17 (wOf (wM i)) (Fi22OutT.L (147 + i)) = true := by
  interval_cases i
  exacts [MK.m0, MK.m1, MK.m2, MK.m3]

theorem evM {i : Nat} (hi : i < 4) :
    fi22OuterPerm3510 (147 + i) = evalWord (fun h : Fin 17 => permOfArr 3510 (fi22OuterStrong3510 3)[h.val]!)
        (CFSG.Monster.B.Co2.toLetters 17 (wOf (wM i))) ∧
      fi22OuterPerm3510 (147 + i) ∈ Orb.Gen 3510 (fi22OuterStrong3510 3) 3 :=
  mem_Gen_of_wordEqK Fi22C3150.hdM ⟨sizeM, Fi22C3150.bindsM.2.2.2.2.1⟩
    (Orb.head_facts Fi22MR.head).1 (wordM hi) (Fi22F1O.arr3510_eq (by omega))
    (rep_fi22OuterPerm3510 (by omega))

theorem sift4 : ∀ i < 4, siftA 3510 (rawLevels 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3])
    #[0, 1, 2, 6, 4, 3] 0 (fi22OuterArr3510 (147 + i)) = true := fun i hi =>
  (siftA_iff_mem_originalSubgroup fi22OuterChainM_arrays (by norm_num) fi22Local_check.1
    (rep_fi22OuterPerm3510 (L := 147 + i) (by omega))).2 (genM_le (evM hi).2)

theorem codesOK : (W3510.w0.all fun x => decide (x / 2 < 17)) &&
    (W3510.w1.all fun x => decide (x / 2 < 17)) && (W3510.w2.all fun x => decide (x / 2 < 17)) &&
    (W3510.w3.all fun x => decide (x / 2 < 17)) = true := by
  decide +kernel

theorem codesLt_of {u : List Nat} (h : (u.all fun x => decide (x / 2 < 17)) = true) :
    codesLt 17 u := fun x hx => by
  simpa using List.all_eq_true.1 h x hx

theorem central : eqA 3510 (compA 3510 (commA 3510 (fi22OuterArr3510 147) (fi22OuterArr3510 148))
    (commA 3510 (fi22OuterArr3510 149) (fi22OuterArr3510 150))) (fi22OuterArr3510 1) = true := by
  refine (eqA_iff (rep_compA (rep_commA (by norm_num) (by norm_num))
    (rep_commA (by norm_num) (by norm_num))) (rep_fi22OuterPerm3510 (L := 1) (by norm_num))).2 ?_
  have hz := (mem_Gen_of_wordEqK Fi22C3150.hdM ⟨sizeM, Fi22C3150.bindsM.2.2.2.2.1⟩
    (Orb.head_facts Fi22MR.head).1 MK.mz (Fi22F1O.arr3510_eq (by norm_num))
    (rep_fi22OuterPerm3510 (L := 1) (by norm_num))).1
  rw [hz, commC]
  simp only [toLetters_append, evalWord_append]
  have hc := codesOK
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c0, c1⟩, c2⟩, c3⟩ := hc
  rw [evalWord_ninvC _ (codesLt_of c0), evalWord_ninvC _ (codesLt_of c1),
    evalWord_ninvC _ (codesLt_of c2), evalWord_ninvC _ (codesLt_of c3)]
  have e0 := (evM (i := 0) (by norm_num)).1
  have e1 := (evM (i := 1) (by norm_num)).1
  have e2 := (evM (i := 2) (by norm_num)).1
  have e3 := (evM (i := 3) (by norm_num)).1
  change fi22OuterPerm3510 147 = _ at e0
  change fi22OuterPerm3510 148 = _ at e1
  change fi22OuterPerm3510 149 = _ at e2
  change fi22OuterPerm3510 150 = _ at e3
  change _ = evalWord _ (CFSG.Monster.B.Co2.toLetters 17 (wOf W3510.w0)) at e0
  change _ = evalWord _ (CFSG.Monster.B.Co2.toLetters 17 (wOf W3510.w1)) at e1
  change _ = evalWord _ (CFSG.Monster.B.Co2.toLetters 17 (wOf W3510.w2)) at e2
  change _ = evalWord _ (CFSG.Monster.B.Co2.toLetters 17 (wOf W3510.w3)) at e3
  rw [← e0, ← e1, ← e2, ← e3]
  group

theorem facts8125 :
    rawChainOK 693 ((fi22OuterStrong693 3).extract 0 fi22OuterM693GenCount)
      (fi22OuterStrong693 3) #[0, 1, 3, 9, 45]
      (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations) 4 = true ∧
    rawOrbitSizes 693 (fi22OuterStrong693 3) #[0, 1, 3, 9, 45] = [693, 512, 120, 36, 6] ∧
    (∀ k < 3, siftA 693 (rawLevels 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45])
      #[0, 1, 3, 9, 45] 0 (fi22OuterArr693 (64 + k)) = true) ∧
    fi22OuterMPointsNat.Nodup ∧
    (∀ k < 3, ∀ j < 693,
      fi22OuterMPointsNat.getD ((invCand 693 (fi22OuterArr693 0))[
        (fi22OuterArr693 (64 + k))[(fi22OuterArr693 0)[j]!]!]!) 0 =
      (fi22OuterArr3510 (3 + k))[fi22OuterMPointsNat.getD j 0]!) ∧
    (∀ j < 693, (fi22OuterArr3510 1)[fi22OuterMPointsNat.getD j 0]! =
      fi22OuterMPointsNat.getD j 0) ∧
    (∀ i < 4, siftA 3510 (rawLevels 3510 (fi22OuterStrong3510 3) #[0, 1, 2, 6, 4, 3])
      #[0, 1, 2, 6, 4, 3] 0 (fi22OuterArr3510 (147 + i)) = true) ∧
    eqA 3510 (compA 3510 (commA 3510 (fi22OuterArr3510 147) (fi22OuterArr3510 148))
      (commA 3510 (fi22OuterArr3510 149) (fi22OuterArr3510 150))) (fi22OuterArr3510 1) = true :=
  ⟨chainM, orbitsM, sift3, nodup, restrict, zfix, sift4, central⟩

end CertificateChecks.KernelFi22U.C8125

end
