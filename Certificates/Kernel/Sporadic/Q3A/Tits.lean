module

public import Certificates.Kernel.Sporadic.Q3A.Main
public import Certificates.Kernel.Sporadic.Q3A.KT

public section

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.Q3A.Check CFSG.Sporadic.SuzRecog.Q3A.TitsCheck
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Q3AK
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem hex1 {cs : List Char} {s : String} {F : Nat → Nat} (hs : s = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 1782 11 1 F = true) :
    hexTable 3 1782 0 s = unpack 1782 11 (F 0) := by
  have h' := CFSG.KC.Misc.HexFlat.hexTable_sound h 0 (by norm_num)
  rw [Nat.mul_zero, ← hs] at h'
  exact h'

theorem tcan : cn W0 = true ∧ cn TAU = true ∧ cn RH0 = true ∧ cn S1 = true ∧ cn S2 = true ∧
    cn (ST 0) = true ∧ cn (ST 1) = true ∧ cn (ST 2) = true := by
  have h := tCan
  simp only [band] at h
  exact h

theorem pW0 : P CFSG.Sporadic.SuzRecog.LevelTwoData.w0Arr W0 := SuzTwCF.pW0
theorem pTau : P CFSG.Sporadic.SuzRecog.Q3ATitsData.tau0Arr TAU :=
  ⟨hex1 Q3ATau.eq Q3ATau.all, tcan.2.1⟩
theorem pRh0 : P CFSG.Sporadic.SuzRecog.Q3ATitsData.rho0Arr RH0 :=
  ⟨hex1 Q3ARho0.eq Q3ARho0.all, tcan.2.2.1⟩
theorem pS1 : P CFSG.Sporadic.SuzRecog.ModelGroupsData.s1Arr S1 :=
  ⟨hex1 SuzMGS1.eq SuzMGS1.all, tcan.2.2.2.1⟩
theorem pS2 : P CFSG.Sporadic.SuzRecog.ModelGroupsData.s2Arr S2 :=
  ⟨hex1 SuzMGS2.eq SuzMGS2.all, tcan.2.2.2.2.1⟩
theorem ST0 : ST 0 = Q3ASt0.F 0 := by
  unfold Q3AK.ST
  rw [nIf_eq, ite_eq_left (Nat.beq_refl 0)]

theorem ST1 : ST 1 = Q3ASt1.F 0 := by
  unfold Q3AK.ST
  rw [nIf_eq, ite_eq_right (by decide), nIf_eq, ite_eq_left (Nat.beq_refl 1)]

theorem ST2 : ST 2 = Q3ASt2.F 0 := by
  unfold Q3AK.ST
  rw [nIf_eq, ite_eq_right (by decide), nIf_eq, ite_eq_right (by decide)]

theorem pSt0 : P CFSG.Sporadic.SuzRecog.Q3ATitsData.stab0Arr (ST 0) := by
  have hc := tcan.2.2.2.2.2.1
  rw [ST0] at hc ⊢
  exact ⟨hex1 Q3ASt0.eq Q3ASt0.all, hc⟩

theorem pSt1 : P CFSG.Sporadic.SuzRecog.Q3ATitsData.stab1Arr (ST 1) := by
  have hc := tcan.2.2.2.2.2.2.1
  rw [ST1] at hc ⊢
  exact ⟨hex1 Q3ASt1.eq Q3ASt1.all, hc⟩

theorem pSt2 : P CFSG.Sporadic.SuzRecog.Q3ATitsData.stab2Arr (ST 2) := by
  have hc := tcan.2.2.2.2.2.2.2
  rw [ST2] at hc ⊢
  exact ⟨hex1 Q3ASt2.eq Q3ASt2.all, hc⟩

theorem pStab {k : Nat} (hk : k < 3) : P (stabA k) (ST k) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · have e : stabA 0 = CFSG.Sporadic.SuzRecog.Q3ATitsData.stab0Arr := ite_eq_left rfl
    rw [e]
    exact pSt0
  · have e : stabA 1 = CFSG.Sporadic.SuzRecog.Q3ATitsData.stab1Arr :=
      (ite_eq_right (by decide)).trans (ite_eq_left rfl)
    rw [e]
    exact pSt1
  · have e : stabA 2 = CFSG.Sporadic.SuzRecog.Q3ATitsData.stab2Arr :=
      (ite_eq_right (by decide)).trans (ite_eq_right (by decide))
    rw [e]
    exact pSt2

theorem tinv : invEqK 1782 11 (mask 11) (1782 * 11) W0 (Q3AI 10) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) TAU (Q3AI 5) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) RH0 (Q3AI 6) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) S1 (Q3AI 11) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) S2 (Q3AI 12) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) (ST 0) (Q3AI 7) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) (ST 1) (Q3AI 8) = true ∧
    invEqK 1782 11 (mask 11) (1782 * 11) (ST 2) (Q3AI 9) = true := by
  have h := tInv
  simp only [band] at h
  exact h

theorem tmem : OddCore.msift W0 = true ∧ OddCore.msift TAU = true ∧ OddCore.msift RH0 = true ∧
    OddCore.msift S1 = true ∧ OddCore.msift S2 = true ∧ OddCore.msift (ST 0) = true ∧
    OddCore.msift (ST 1) = true ∧ OddCore.msift (ST 2) = true := by
  have h1 := tMemA
  have h2 := tMemB
  simp only [band] at h1 h2
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

theorem gen_ok {a : Array Nat} {A AI : Nat} (ha : P a A)
    (hi : invEqK 1782 11 (mask 11) (1782 * 11) A AI = true) (hc : cn AI = true)
    (hm : OddCore.msift A = true) :
    isInvA 1782 a (invCand 1782 a) = true ∧ CFSG.Sporadic.SuzOddCore.inM a = true := by
  rw [(pInv ha hi hc).2, OddCore.inM_eq ha.1 ha.2, hm]
  exact ⟨rfl, rfl⟩

theorem img_id {X : Nat} (hX : ∀ t < 162, pg 11 (mask 11) X t < 1782) :
    imgA (idA 1782) (unpack 162 11 X) = unpack 162 11 X := by
  apply Array.ext
  · simp only [imgA, Array.size_map]
  · intro t h1 h2
    have ht : t < 162 := by rwa [unpack_size] at h2
    simp only [imgA, Array.getElem_map]
    rw [unpack_getElem, CFSG.Monster.B.Co2.idA_get (hX t ht)]

theorem act_id {y : Nat} (hy : y < 22880) : actIdx (idA 1782) y = y := by
  obtain ⟨e1, e2⟩ := fimg_FL hv hy
  unfold actIdx
  rw [e1, img_id e2, keyIdx_eq hv, keyOf_FL ⟨rfl, e2⟩]
  exact (vt_parts hv hy).2.1

theorem tacts : actK W0 0 = 58 ∧ actK RH0 58 = 2622 ∧ actK S1 58 = 2158 ∧ frootK 58 = 10 ∧
    actK (pidn 1782 11) 58 = 58 ∧ actK W0 58 = 0 ∧ actK TAU 0 = 58 ∧ actK TAU 58 = 0 ∧
    actK TAU 2622 = 2622 ∧ actK RH0 0 = 58 ∧ actK RH0 2622 = 0 ∧ actK S1 0 = 0 ∧
    actK S1 2158 = 58 ∧ actK S2 0 = 58 ∧ actK S2 58 = 0 ∧ actK S2 2158 = 2158 := by
  have h := tAct
  simp only [band, nbeq] at h
  exact h

theorem iv1_eq : iv1 = 58 := by
  unfold iv1
  rw [actIdx_eq hv pW0 (by norm_num)]
  exact tacts.1

theorem iu0_eq : iu0 = 2622 := by
  unfold iu0
  rw [iv1_eq, actIdx_eq hv pRh0 (by norm_num)]
  exact tacts.2.1

theorem iu1_eq : iu1 = 2158 := by
  unfold iu1
  rw [iv1_eq, actIdx_eq hv pS1 (by norm_num)]
  exact tacts.2.2.1

theorem adjIdx0 {y : Nat} (hy : y < 22880) : adjIdx 0 y = isNbr0 y := by
  unfold adjIdx
  have h0 : cArrInv 0 = idA 1782 := by
    rw [cArrInv_eq, ite_eq_right (by omega)]
  rw [h0, act_id hy]

theorem opar_get {y : Nat} (hy : y < 22880) : opar[y]! = oparK y := by
  unfold opar
  exact hx_get Q3AOP.eq Q3AOP.all hy

theorem olab_get {y : Nat} (hy : y < 22880) : olab[y]! = olabK y := by
  unfold olab
  exact hx_get Q3AOL.eq Q3AOL.all hy

theorem odep_get {y : Nat} (hy : y < 22880) : odep[y]! = odepK y := by
  unfold odep
  exact hx_get Q3AOD.eq Q3AOD.all hy

theorem forestCheck_true : forestCheck = true := by
  unfold forestCheck
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true,
    and_assoc]
  refine ⟨by unfold opar; exact hexTable_size, by unfold olab; exact hexTable_size,
    by unfold odep; exact hexTable_size, fun y hy => ?_⟩
  have h := allN_get tForest hy
  unfold otOK at h
  rw [sB, bIf_eq] at h
  rw [opar_get hy, odep_get hy, olab_get hy, iu0_eq, iu1_eq]
  by_cases hp : oparK y = 22880
  · exact Or.inl hp
  right
  rw [ite_eq_right (by rw [nbeq]; exact hp), bIf_eq] at h
  by_cases hd : odepK y = 0
  · rw [ite_eq_left (nbeq.2 hd), bIf_eq] at h
    rw [ite_eq_left (by simpa using hd)]
    simp only [Bool.or_eq_true, beq_iff_eq]
    by_cases h1 : y = 2622
    · exact Or.inl h1
    · rw [ite_eq_right (by rw [nbeq]; exact h1)] at h
      exact Or.inr (nbeq.1 h)
  · rw [ite_eq_right (by rw [nbeq]; exact hd)] at h
    rw [ite_eq_right (by simpa using hd)]
    simp only [band] at h
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have h1' := nblt.1 h1
    rw [opar_get h1', odep_get h1']
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨⟨⟨⟨h1', nblt.1 h2⟩, nblt.1 h3⟩, nblt.1 h4⟩, ?_⟩
    rw [actIdx_eq hv (pStab (nblt.1 h4)) h1']
    exact nbeq.1 h5

theorem common {y : Nat} (hy : y < 22880) (h0 : isNbr0 y = true)
    (h1 : adjWith (cArrInv 58) y = true) : opar[y]! < 22880 := by
  have hm : y ∈ nbr0 := Array.mem_filter.2 ⟨Array.mem_range.2 hy, h0⟩
  rw [nbr0_eq hv hf, List.mem_toArray] at hm
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hm
  have h := allN_get tCommon (List.mem_range.1 ht)
  rw [sB, bIf_eq, ite_eq_left] at h
  · rw [opar_get hy]
    exact nblt.1 h
  · unfold adjWith at h1
    rw [actIdx_eq hv (p_cArrInv hv (by norm_num)) hy] at h1
    rw [nbeq.1 tCI, adjK_iff]
    exact (isNbr0_iff hv hf _).1 h1

theorem titsCheck_true : titsCheck = true := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := tacts
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := tinv
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := tmem
  have c := cI (j := 10) (by norm_num)
  unfold titsCheck
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true,
    decide_eq_true_eq, and_assoc, List.all_eq_true, List.mem_range]
  rw [iv1_eq, iu0_eq, iu1_eq]
  refine ⟨fun a ha => ?_, pRhoI.2, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_, forestCheck_true, fun y hy => ?_⟩
  · simp only [gensT, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with h | h | h | h | h | h | h | h <;> rw [h]
    · exact gen_ok pW0 i1 c m1
    · exact gen_ok pTau i2 (cI (by norm_num)) m2
    · exact gen_ok pRh0 i3 (cI (by norm_num)) m3
    · exact gen_ok pS1 i4 (cI (by norm_num)) m4
    · exact gen_ok pS2 i5 (cI (by norm_num)) m5
    · exact gen_ok pSt0 i6 (cI (by norm_num)) m6
    · exact gen_ok pSt1 i7 (cI (by norm_num)) m7
    · exact gen_ok pSt2 i8 (cI (by norm_num)) m8
  · rw [adjIdx0 (by norm_num), isNbr0_iff hv hf]
    exact ⟨by norm_num, a4⟩
  · rw [actIdx_eq hv pW0 (by norm_num), a6]
  · rw [actIdx_eq hv pTau (by norm_num), a7]
  · rw [actIdx_eq hv pTau (by norm_num), a8]
  · rw [actIdx_eq hv pTau (by norm_num), a9]
  · rw [actIdx_eq hv pRh0 (by norm_num), a10]
  · rw [actIdx_eq hv pRh0 (by norm_num), a11]
  · rw [actIdx_eq hv pS1 (by norm_num), a12]
  · rw [actIdx_eq hv pS1 (by norm_num), a13]
  · rw [actIdx_eq hv pS2 (by norm_num), a14]
  · rw [actIdx_eq hv pS2 (by norm_num), a15]
  · rw [actIdx_eq hv pS2 (by norm_num), a16]
  · have h := allN_get tStab hk
    rw [band, nbeq, nbeq] at h
    rw [actIdx_eq hv (pStab hk) (by norm_num), actIdx_eq hv (pStab hk) (by norm_num)]
    exact h
  · have hw := (pInv pW0 i1 c).1
    have hr2 : P rho2A RHO2 := p_comp pW0 (p_comp pRho hw)
    have hri := (pInv pRh0 i3 (cI (by norm_num))).1
    rw [eqA_P (p_comp (p_comp pRh0 (p_comp hr2 hri)) (p_comp hr2 pRho)) pidn_P]
    exact tRel
  · by_cases h0 : isNbr0 y = true
    · by_cases h1 : adjWith (cArrInv 58) y = true
      · exact Or.inr (common hy h0 h1)
      · left
        rw [adjIdx0 hy, h0, Bool.eq_false_iff.2 h1]
        rfl
    · left
      rw [adjIdx0 hy, Bool.eq_false_iff.2 h0]
      rfl

end CertificateChecks.KernelSpor.Q3AG

end
