module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThListFacts
public import CFSG.Certificates.Kernel.ThCent.ListSound
public import Certificates.Kernel.ThCent.Consumers
public import Certificates.Kernel.ThCent.LDefs
public import Certificates.Kernel.ThCent.L7Pin
public import Certificates.Kernel.ThCent.L5Pin
public import Certificates.Kernel.ThCent.L7C0
public import Certificates.Kernel.ThCent.L7C1
public import Certificates.Kernel.ThCent.L5C0
public import Certificates.Kernel.ThCent.L5C1
public import Certificates.Kernel.ThCent.L5C2
public import Certificates.Kernel.ThCent.L5C3
public import Certificates.Kernel.ThCent.L7Misc
public import Certificates.Kernel.ThCent.L5Misc
public import Certificates.Kernel.ThCent.L5Dist
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelThList

open CFSG.Sporadic.Th CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel
  CFSG.KC.ThCent CFSG.KD.ThCent.L CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlp
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList CFSG.SectionRank.Native CFSG.KD

set_option maxRecDepth 100000

local notation "𝕄" g:max =>
  ((Subtype.val g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

#kc_forall_tree ch7_all (fun k => CFSG.KD.ThCent.L.ch7 k = true) 24 CFSG.KD.ThCent.L.ch7_
#kc_forall_tree ch5_all (fun k => CFSG.KD.ThCent.L.ch5 k = true) 60 CFSG.KD.ThCent.L.ch5_
#kc_forall_tree conj7_all (fun k => CFSG.KD.ThCent.L.conj7F k = true) 7 CFSG.KD.ThCent.L.conj7_
#kc_forall_tree conj5_all (fun k => CFSG.KD.ThCent.L.conj5F k = true) 5 CFSG.KD.ThCent.L.conj5_
#kc_forall_tree row5_all (fun k => CFSG.KD.ThCent.L.row5F k = true) 5 CFSG.KD.ThCent.L.row5_


theorem mat_inj {g h : J} (e : 𝕄 g = 𝕄 h) : g = h := mat_injective e

theorem mat_word {V : ℕ → ℕ} {R : ℕ → J} {S : List ℕ} (hV : ∀ r ∈ S, 𝕄 (R r) = pkMat (V r))
    {w : List ℕ} (hw : ∀ r ∈ w, r ∈ S) :
    𝕄 ((w.map R).prod) = pkMat (wordR ThS.c ThS.rm ThS.ONE V w) := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  rw [mat_list_prod, pkMat_wordR hk, List.map_map]
  congr 1
  exact List.map_congr_left fun r hr => hV r (hw r hr)

theorem mat_reg (prog : List Op) (hp : powsOK prog = true) (r : ℕ) :
    pkMat (runPk ThS.c ThS.rm ThS.ONE prog (initPk (ThS.RBf 1) (ThS.RBf 2) ThS.ONE) r) =
      𝕄 (slpJ a b prog r) := by
  obtain ⟨hA, hB, -, hk⟩ := KernelThCent.fwd_mats
  rw [KernelThCent.slpJ_eq]
  exact pkMat_runPk hk prog hp _ _ (pkMat_initPk hk a b hA hB) r

theorem regsOK_spec {S : List ℕ} {E : List (List ℕ × List (List ℕ × List ℕ) × ℕ)}
    (h : (E.all fun e => e.1.all (fun r => S.elem r) &&
      e.2.1.all fun p => p.1.all (fun r => S.elem r) && p.2.all (fun r => S.elem r)) = true)
    (i : ℕ) (hi : i < E.length) :
    (∀ r ∈ (E[i]).1, r ∈ S) ∧ ∀ p ∈ (E[i]).2.1, (∀ r ∈ p.1, r ∈ S) ∧ ∀ r ∈ p.2, r ∈ S := by
  have := List.all_eq_true.1 h _ (List.getElem_mem hi)
  simp only [Bool.and_eq_true, List.all_eq_true, List.elem_eq_mem, decide_eq_true_eq] at this
  exact ⟨this.1, fun p hp => this.2 p hp⟩

theorem list_facts {V : ℕ → ℕ} {R : ℕ → J} {S : List ℕ} (hV : ∀ r ∈ S, 𝕄 (R r) = pkMat (V r))
    {E : List (List ℕ × List (List ℕ × List ℕ) × ℕ)} {n : ℕ} (hn : E.length = n)
    {Z : ℕ} {z : J} (hZ : 𝕄 z = pkMat Z)
    (hall : ∀ i (hi : i < E.length), eltRec ThS.c ThS.rm ThS.ONE V Z 24 (E[i]) = true)
    (hregs : (E.all fun e => e.1.all (fun r => S.elem r) &&
      e.2.1.all fun p => p.1.all (fun r => S.elem r) && p.2.all (fun r => S.elem r)) = true)
    (hdist : distinctL (E.map fun e => e.2.2) = true)
    (words : ℕ → List ℕ) (hw : ∀ i (hi : i < E.length), (E[i]).1 = words i)
    (wit : ℕ → List ℕ) (inv : ℕ → ℕ)
    (hwit : ∀ i (hi : i < E.length), (E[i]).2.1 = (wit i).map fun j => (words j, words (inv j))) :
    (∀ i < n, ((words i).map R).prod * z = z * ((words i).map R).prod) ∧
      (∀ i < n, ∀ j < i, ((words i).map R).prod ≠ ((words j).map R).prod) ∧
      (∀ i < n, ((words i).map R).prod ≠ 1 →
        (((words i).map R).prod * ((wit i).map fun j =>
          ((words j).map R).prod * ((words i).map R).prod * (((words j).map R).prod)⁻¹).prod) ^ 24
            ≠ 1) := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  subst hn
  have hel : ∀ i (hi : i < E.length), 𝕄 (((words i).map R).prod) =
      pkMat (wordR ThS.c ThS.rm ThS.ONE V (E[i]).1) := by
    intro i hi
    rw [hw i hi]
    exact mat_word hV (by rw [← hw i hi]; exact (regsOK_spec hregs i hi).1)
  have hsound := fun i (hi : i < E.length) => eltOK_sound hk (by norm_num) (hall i hi)
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_, fun i hi hne => ?_⟩
  · apply mat_inj
    rw [mat_mul, mat_mul, hel i hi, hZ]
    exact (hsound i hi).1
  · intro e
    have hjE : j < E.length := hj.trans hi
    have hrow : (E[i]).2.2 ≠ (E[j]).2.2 := by
      have hnd := distinctL_sound _ hdist
      have := (List.Nodup.getElem_inj_iff hnd (i := i) (j := j) (hi := by simpa using hi)
        (hj := by simpa using hjE)).not.2 (by omega)
      simpa using this
    rw [← (hsound i hi).2.1, ← (hsound j hjE).2.1] at hrow
    apply ne_of_rowB hk hrow
    rw [← hel i hi, ← hel j hjE, e]
  · rcases (hsound i hi).2.2 with h1 | ⟨hpow, hinv⟩
    · exact absurd (mat_inj (by rw [hel i hi, h1, mat_one])) hne
    · intro e
      apply hpow
      have hmap : ((E[i]).2.1.map fun p => pkMat (wordR ThS.c ThS.rm ThS.ONE V p.1) *
          pkMat (wordR ThS.c ThS.rm ThS.ONE V (E[i]).1) *
            pkMat (wordR ThS.c ThS.rm ThS.ONE V p.2)) =
          ((wit i).map fun j => 𝕄 (((words j).map R).prod * ((words i).map R).prod *
            (((words j).map R).prod)⁻¹)) := by
        rw [hwit i hi, List.map_map]
        apply List.map_congr_left
        intro j hj
        have hp : (words j, words (inv j)) ∈ (E[i]).2.1 := by
          rw [hwit i hi]
          exact List.mem_map_of_mem hj
        obtain ⟨hp1, hp2⟩ := (regsOK_spec hregs i hi).2 _ hp
        have e1 : 𝕄 (((words j).map R).prod) = pkMat (wordR ThS.c ThS.rm ThS.ONE V (words j)) :=
          mat_word hV hp1
        have e2 := hinv _ hp
        simp only at e2 hp2 ⊢
        rw [mat_mul, mat_mul, e1, hel i hi, mat_inv_eq (by rw [e1]; exact e2)]
        rfl
      have hl : ((wit i).map fun j => 𝕄 (((words j).map R).prod * ((words i).map R).prod *
            (((words j).map R).prod)⁻¹)) =
          ((wit i).map fun j => ((words j).map R).prod * ((words i).map R).prod *
            (((words j).map R).prod)⁻¹).map fun g => 𝕄 g := by
        rw [List.map_map]
        rfl
      rw [hmap, ← hel i hi, hl, ← mat_list_prod, ← mat_mul, ← mat_pow, e, mat_one]

theorem getElem!_of_toList {α : Type} [Inhabited α] (A : Array α) {i : ℕ} (hi : i < A.toList.length) :
    A.toList[i] = A[i]! := by
  rw [getElem!_pos A i (by simpa using hi)]
  rfl

theorem words_of_map {α : Type} [Inhabited α] {E : List (α × List (List ℕ × List ℕ) × ℕ)}
    {A : Array α} (h : E.map (fun e => e.1) = A.toList) (i : ℕ) (hi : i < E.length) :
    (E[i]).1 = A[i]! := by
  have hl : i < A.toList.length := by rw [← h, List.length_map]; exact hi
  rw [← getElem!_of_toList A hl]
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hl,
    Option.map_some] at this
  exact Option.some.inj this

theorem wit_of_map {α : Type} {E : List (α × List (List ℕ × List ℕ) × ℕ)}
    {A : Array (List ℕ)} {F : List ℕ → List (List ℕ × List ℕ)}
    (h : E.map (fun e => e.2.1) = A.toList.map F) (i : ℕ) (hi : i < E.length) :
    (E[i]).2.1 = F (A[i]!) := by
  have hl : i < A.toList.length := by
    have := congrArg List.length h
    simp only [List.length_map] at this
    omega
  rw [← getElem!_of_toList A hl]
  have := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hl,
    Option.map_some] at this
  exact Option.some.inj this

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative in
theorem mat_R7 : ∀ r ∈ regs7, 𝕄 (slpJ a b prog7 r) = pkMat (V7 r) := by
  intro r hr
  rw [← mat_reg prog7 (by decide +kernel) r]
  simp only [regs7, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Nat.eq_of_beq_eq_true pin7_2]
  · rw [Nat.eq_of_beq_eq_true pin7_3]
  · rw [Nat.eq_of_beq_eq_true pin7_24]
  · rw [Nat.eq_of_beq_eq_true pin7_25]
  · rw [Nat.eq_of_beq_eq_true pin7_31]
  · rw [Nat.eq_of_beq_eq_true pin7_34]
  · rw [Nat.eq_of_beq_eq_true pin7_39]
  · rw [Nat.eq_of_beq_eq_true pin7_40]
  · rw [Nat.eq_of_beq_eq_true pin7_41]
  · rw [Nat.eq_of_beq_eq_true pin7_42]

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative in
theorem mat_R5 : ∀ r ∈ regs5, 𝕄 (slpJ a b prog5 r) = pkMat (V5 r) := by
  intro r hr
  rw [← mat_reg prog5 (by decide +kernel) r]
  simp only [regs5, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [Nat.eq_of_beq_eq_true pin5_19]
  · rw [Nat.eq_of_beq_eq_true pin5_25]
  · rw [Nat.eq_of_beq_eq_true pin5_82]
  · rw [Nat.eq_of_beq_eq_true pin5_84]
  · rw [Nat.eq_of_beq_eq_true pin5_94]
  · rw [Nat.eq_of_beq_eq_true pin5_99]
  · rw [Nat.eq_of_beq_eq_true pin5_105]
  · rw [Nat.eq_of_beq_eq_true pin5_114]
  · rw [Nat.eq_of_beq_eq_true pin5_115]
  · rw [Nat.eq_of_beq_eq_true pin5_116]
  · rw [Nat.eq_of_beq_eq_true pin5_117]

theorem regs_of_all {S : List ℕ} {l : List ℕ} (h : (l.all fun r => S.elem r) = true) :
    ∀ r ∈ l, r ∈ S := by
  intro r hr
  have := List.all_eq_true.1 h r hr
  simpa using this

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSevenNative in
theorem th_seven_facts : ThSevenFacts := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hx := mat_R7 24 (by decide)
  have hy := mat_R7 25 (by decide)
  have hz : 𝕄 z7 = pkMat CFSG.KD.ThCent.W.Z7 := KernelThCent.mat_z7
  obtain ⟨p1, p2, p3, p4, p5⟩ := pairOK7_sound hk pair7_ok
  have hL := list_facts mat_R7 E7_length hz
    (all_of_chunkOK _ CFSG.KD.ThCent.L7.E 49 24 (by rw [E7_length]) fun k hk' => ch7_all k hk')
    E7_regs dist7_ok (fun i => list7.words[i]!) (words_of_map E7_words)
    (fun i => list7.wit[i]!) (fun j => list7.inv[j]!) (wit_of_map E7_wit)
  refine ⟨mat_inj (by rw [mat_pow, hx, p1, mat_one]), mat_inj (by rw [mat_pow, hy, p2, mat_one]),
    mat_inj (by rw [mat_mul, mat_mul, hx, hy, p3]),
    fun e => p4 (by rw [← hx, e, mat_one]),
    fun k hk7 e => p5 k hk7 (by rw [← hy, ← hx, ← mat_pow, e]), ?_, hL.1, hL.2.1, hL.2.2⟩
  intro i j hi hj hij
  have hc := List.all_eq_true.1 (conj7_all i hi) j (List.mem_range.2 hj)
  rcases Bool.or_eq_true_iff.1 hc with h0 | hc
  · exact absurd (Nat.eq_of_beq_eq_true h0) hij
  have hm := conjOK7_sound hk (by omega) (by omega) hc
  have hreg : ∀ r ∈ conj7[7 * i + j]!, r ∈ regs7 := regs_of_all (by
    have := List.all_eq_true.1 conj7_regs (7 * i + j) (List.mem_range.2 (by omega))
    exact this)
  refine ⟨((conj7[7 * i + j]!).map (slpJ a b prog7)).prod, mat_inj ?_⟩
  rw [mat_mul, mat_mul, mat_mul, mat_pow, mat_pow, mat_word mat_R7 hreg, hx, hy, hz, hm]

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThFiveNative in
theorem th_five_facts : ThFiveFacts := by
  obtain ⟨-, -, -, hk⟩ := KernelThCent.fwd_mats
  have hx := mat_R5 94 (by decide)
  have hy := mat_R5 105 (by decide)
  have hc : 𝕄 c5 = pkMat C5 := by
    unfold c5 C5
    rw [mat_mul, mat_mul, mat_mul, mat_pow, mat_pow, hx, hy, pkMat_mulB hk, pkMat_mulB hk,
      pkMat_mulB hk, pkMat_powB hk _ _ 3 (by norm_num), pkMat_powB hk _ _ 3 (by norm_num)]
  have hcube : cubeOK5 ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C5 = true := by
    have := cube5_ok
    unfold cube5 at this
    rwa [strictF_eq] at this
  obtain ⟨q1, q2, q3, q4⟩ := cubeOK5_sound hk hcube
  have hL := list_facts mat_R5 E5_length hc
    (by
      intro i hi
      refine all_of_chunkOK _ CFSG.KD.ThCent.L5.E 50 60 (by rw [E5_length]) (fun k hk' => ?_) i hi
      have := ch5_all k hk'
      unfold ch5 at this
      rwa [strictF_eq] at this)
    E5_regs dist5_ok (fun i => list5.words[i]!) (words_of_map E5_words)
    (fun i => list5.wit[i]!) (fun j => list5.inv[j]!) (wit_of_map E5_wit)
  have hP : ∀ i j k : ℕ, i < 8 → j < 8 → k < 8 →
      𝕄 (slpJ a b prog5 94 ^ i * slpJ a b prog5 105 ^ j * c5 ^ k) =
        pkMat (cubeP ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C5 i j k) := by
    intro i j k hi hj hk'
    rw [pkMat_cubeP hk hi hj hk', mat_mul, mat_mul, mat_pow, mat_pow, mat_pow, hx, hy, hc]
  have hrow : ∀ i j k : ℕ, i < 5 → j < 5 → k < 5 →
      rowB ThS.rm (cubeP ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C5 i j k) 0 =
        CFSG.KD.ThCent.L5.RC.getD (25 * i + 5 * j + k) 0 := by
    intro i j k hi hj hk'
    have h1 := row5_all i hi
    unfold row5F at h1
    rw [strictF_eq] at h1
    have h2 := List.all_eq_true.1 h1 (5 * j + k) (List.mem_range.2 (by omega))
    have e1 : (5 * j + k) / 5 = j := by omega
    have e2 : (5 * j + k) % 5 = k := by omega
    have e3 : 25 * i + (5 * j + k) = 25 * i + 5 * j + k := by omega
    rw [e1, e2, e3] at h2
    exact Nat.eq_of_beq_eq_true h2
  have hnd := distinctL_sound _ distC_ok
  refine ⟨mat_inj (by rw [mat_pow, hx, q1, mat_one]), mat_inj (by rw [mat_pow, hy, q2, mat_one]),
    mat_inj (by rw [mat_mul, mat_mul, hx, hc, q3]), mat_inj (by rw [mat_mul, mat_mul, hy, hc, q4]),
    ?_, ?_, hL.1, hL.2.1, hL.2.2⟩
  · intro i j k i' j' k' hi hj hk' hi' hj' hk'' e
    have e1 : rowB ThS.rm (cubeP ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C5 i j k) 0 =
        rowB ThS.rm (cubeP ThS.c ThS.rm ThS.ONE (V5 94) (V5 105) C5 i' j' k') 0 := by
      by_contra hne
      exact ne_of_rowB hk hne (by rw [← hP i j k (by omega) (by omega) (by omega),
        ← hP i' j' k' (by omega) (by omega) (by omega), e])
    rw [hrow i j k hi hj hk', hrow i' j' k' hi' hj' hk''] at e1
    have hlen := RC_length
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e1
    have := (List.Nodup.getElem_inj_iff hnd).1 e1
    omega
  · intro i j k hi hj hk' hijk
    have h1 := conj5_all i hi
    unfold conj5F at h1
    rw [strictF_eq] at h1
    have h2 := List.all_eq_true.1 h1 (5 * j + k) (List.mem_range.2 (by omega))
    rcases Bool.or_eq_true_iff.1 h2 with h0 | h2
    · exact absurd (Nat.eq_of_beq_eq_true h0) (by omega)
    have e1 : (5 * j + k) / 5 = j := by omega
    have e2 : (5 * j + k) % 5 = k := by omega
    have e3 : 25 * i + (5 * j + k) = 25 * i + 5 * j + k := by omega
    rw [e1, e2, e3] at h2
    have hm := conjOK5_sound hk (by omega) (by omega) (by omega) h2
    have hreg : ∀ r ∈ conj5[25 * i + 5 * j + k]!, r ∈ regs5 := regs_of_all (by
      have := List.all_eq_true.1 conj5_regs (25 * i + 5 * j + k) (List.mem_range.2 (by omega))
      exact this)
    refine ⟨((conj5[25 * i + 5 * j + k]!).map (slpJ a b prog5)).prod, mat_inj ?_⟩
    have e := hP i j k (by omega) (by omega) (by omega)
    rw [pkMat_cubeP hk (by omega) (by omega) (by omega)] at e
    rw [mat_mul (_ : J) (slpJ a b prog5 94 ^ i * slpJ a b prog5 105 ^ j * c5 ^ k), mat_mul c5,
      mat_word mat_R5 hreg, e, hc, hm]

end CertificateChecks.KernelThList

end
