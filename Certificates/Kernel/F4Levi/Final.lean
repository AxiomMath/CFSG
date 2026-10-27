module

public import Certificates.Kernel.F4Levi.Checks
public import Certificates.Kernel.F4Levi.Rank
public import Certificates.Kernel.F4Inv.Final
public import CFSG.Certificates.Kernel.F4Gamma.Sound
public import CFSG.LocalAnalysis.StandardType.GGF4TwoRootAsProof
import all CFSG.LieType.Simplicity.TitsBits
import all CFSG.Certificates.Kernel.F4SaltSound

public section

namespace CFSG.KC.F4Levi

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits CFSG.KC.F4Salt CFSG.KC.Loop CFSG.KC.F4Syl3
  CFSG.KC.F4Rank CFSG.KC.F4Inv CFSG.KD.F4Levi CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.TableBF4TwoInputs CFSG.RankThree.PartTwo.Sec4.Item434F42
  CFSG.RankThree.PartTwo.Sec21.FF79 CFSG.RankThree.PartTwo.Sec21.FF79.L41 Module
open CFSG.RankThree.PartOne.SEITZX (wordOfCodes letterOfCode)


noncomputable abbrev Lv2 : Subgroup F42C := C3Levi (ZMod 2)

theorem card_Lv2 : Nat.card ↥Lv2 = 1451520 :=
  card_C3Levi_two (by simp)

noncomputable abbrev wE (W L : ℕ) : F42C := evalG (ZMod 2) (wordOfCodes (decW8 W L))

theorem hasBits_of_eqSL {g : F42C} {A G : ℕ} (hg : HasBitsS (ZMod 2) g A)
    (h : eqS A (saltOf G) = true) : HasBits (ZMod 2) g G := by
  have h1 := (eqS_iff A (saltOf G)).1 h
  rw [dataS_saltOf] at h1
  unfold HasBitsS HasBits at hg
  unfold HasBits
  rw [hg]
  exact (toEnd_eq_toEnd_iff _ _).2 h1

theorem hasBitsS_rA : HasBitsS (ZMod 2) rAE (saltOf (sBits 3)) := by
  rw [sBits_three]
  exact hasBitsS_saltOf hasBits_rAE

theorem gen_mem {l : ℕ} (hl : l < 6) : (letterOfCode (lvC l)).elt (ZMod 2) ∈ Lv2 := by
  have h := beq_iff_eq.1 (CFSG.KC.F4Gamma.allN_true gen_ok l hl)
  simp only [genN, strictN_eq] at h
  have e := toNat_eq_one h
  rw [Bool.and_eq_true] at e
  have hX := hasBitsS_letS (K := ZMod 2) (lvC l)
  have h2 := ((hX.mul hX).eq_iff hasBitsS_one).2 e.1
  have h3 := ((hX.mul hasBitsS_rA).eq_iff (hasBitsS_rA.mul hX)).2 e.2
  exact CFSG.StandardType.F4RootAs.mem_C3Levi_of_commute_nodeElt (by simp) h3
    ((pow_two _).trans h2)

theorem letter_mem {c : ℕ} (hc : c < 8) (h0 : c ≠ 0) (h4 : c ≠ 4) :
    (letterOfCode c).elt (ZMod 2) ∈ Lv2 := by
  by_cases h : c < 4
  · have e : c = lvC (c - 1) := by unfold lvC; split_ifs <;> omega
    rw [e]
    exact gen_mem (by omega)
  · have e : c = lvC (c - 2) := by unfold lvC; split_ifs <;> omega
    rw [e]
    exact gen_mem (by omega)

theorem wE_mem (W : ℕ) : ∀ L, lvOK W L = true → wE W L ∈ Lv2
  | 0, _ => Subgroup.one_mem _
  | L + 1, h => by
    have h' : ((digit W L != 0 && digit W L != 4) && lvOK W L) = true := h
    rw [Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne, bne_iff_ne, digit_eq] at h'
    have e : wE W (L + 1) = wE W L * (letterOfCode (W / 2 ^ (3 * L) % 8)).elt (ZMod 2) := by
      rw [wE, decW8, wordOfCodes, List.map_append, evalG_append, List.map_singleton,
        evalG_singleton]
      rfl
    rw [e]
    exact mul_mem (wE_mem W L h'.2) (letter_mem (Nat.mod_lt _ (by norm_num)) h'.1.1 h'.1.2)

noncomputable def gD (k : ℕ) : F42C := wE (dw.getD k 0) (dl.getD k 0)

theorem gD_spec {k : ℕ} (hk : k < 4) :
    gD k ∈ Lv2 ∧ HasBits (ZMod 2) (gD k) (gs.getD k 0) := by
  have h := CFSG.KC.F4Gamma.allN_true d3_ok k hk
  simp only [d3Row, Bool.and_eq_true] at h
  exact ⟨wE_mem _ _ h.1, hasBits_of_eqSL (hasBitsS_wordS _ _) h.2⟩

noncomputable def eE (i : ℕ) : F42C := wordElt gD (ew.getD i [])

theorem blt_lt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  rwa [Nat.blt_eq] at h

theorem el_row {i m n : ℕ} (h : (elN gs es ew nx m i == n) = true) (hm : m = 81) (hn : n = 1)
    {j : ℕ} (hj : i = j) : (∀ k ∈ ew.getD j [], k < 4) ∧ HasBits (ZMod 2) (eE j) (es.getD j 0) ∧
      ∀ k < 4, nx.getD (4 * j + k) 0 < 81 ∧
        HasBits (ZMod 2) (eE j * gD k) (es.getD (nx.getD (4 * j + k) 0) 0) := by
  subst hm hn hj
  have h := beq_iff_eq.1 h
  simp only [elN, strictN_eq] at h
  have h1' := toNat_eq_one (Nat.eq_one_of_mul_eq_one_right h)
  have h2' := toNat_eq_one (Nat.eq_one_of_mul_eq_one_left h)
  rw [Bool.and_eq_true] at h2'
  have hl : ∀ k ∈ ew.getD i [], k < 4 := fun k hk => blt_lt (List.all_eq_true.1 h1' k hk)
  have hb : HasBits (ZMod 2) (eE i) (es.getD i 0) :=
    hasBits_of_eqSL (CFSG.KC.F4Gamma.hasBitsS_prodS _ fun k hk => (gD_spec (hl k hk)).2) h2'.1
  refine ⟨hl, hb, fun k hk => ?_⟩
  have e := CFSG.KC.F4Gamma.allN_true h2'.2 k hk
  rw [Bool.and_eq_true, Nat.blt_eq] at e
  exact ⟨e.1, hasBits_of_eqSL ((hasBitsS_saltOf hb).mul (hasBitsS_saltOf (gD_spec hk).2)) e.2⟩

theorem el_all : ∀ i < 81, (∀ k ∈ ew.getD i [], k < 4) ∧ HasBits (ZMod 2) (eE i) (es.getD i 0) ∧
    ∀ k < 4, nx.getD (4 * i + k) 0 < 81 ∧
      HasBits (ZMod 2) (eE i * gD k) (es.getD (nx.getD (4 * i + k) 0) 0) := by
  intro i hi
  interval_cases i
  exacts [el_row ch799603el.r0 rfl rfl rfl, el_row ch799603el.r1 rfl rfl rfl,
    el_row ch799603el.r2 rfl rfl rfl, el_row ch799603el.r3 rfl rfl rfl,
    el_row ch799603el.r4 rfl rfl rfl, el_row ch799603el.r5 rfl rfl rfl,
    el_row ch799603el.r6 rfl rfl rfl, el_row ch799603el.r7 rfl rfl rfl,
    el_row ch799603el.r8 rfl rfl rfl, el_row ch799603el.r9 rfl rfl rfl,
    el_row ch799603el.r10 rfl rfl rfl, el_row ch799603el.r11 rfl rfl rfl,
    el_row ch799603el.r12 rfl rfl rfl, el_row ch799603el.r13 rfl rfl rfl,
    el_row ch799603el.r14 rfl rfl rfl, el_row ch799603el.r15 rfl rfl rfl,
    el_row ch799603el.r16 rfl rfl rfl, el_row ch799603el.r17 rfl rfl rfl,
    el_row ch799603el.r18 rfl rfl rfl, el_row ch799603el.r19 rfl rfl rfl,
    el_row ch799603el.r20 rfl rfl rfl, el_row ch799603el.r21 rfl rfl rfl,
    el_row ch799603el.r22 rfl rfl rfl, el_row ch799603el.r23 rfl rfl rfl,
    el_row ch799603el.r24 rfl rfl rfl, el_row ch799603el.r25 rfl rfl rfl,
    el_row ch799603el.r26 rfl rfl rfl, el_row ch799603el.r27 rfl rfl rfl,
    el_row ch799603el.r28 rfl rfl rfl, el_row ch799603el.r29 rfl rfl rfl,
    el_row ch799603el.r30 rfl rfl rfl, el_row ch799603el.r31 rfl rfl rfl,
    el_row ch799603el.r32 rfl rfl rfl, el_row ch799603el.r33 rfl rfl rfl,
    el_row ch799603el.r34 rfl rfl rfl, el_row ch799603el.r35 rfl rfl rfl,
    el_row ch799603el.r36 rfl rfl rfl, el_row ch799603el.r37 rfl rfl rfl,
    el_row ch799603el.r38 rfl rfl rfl, el_row ch799603el.r39 rfl rfl rfl,
    el_row ch799603el.r40 rfl rfl rfl, el_row ch799603el.r41 rfl rfl rfl,
    el_row ch799603el.r42 rfl rfl rfl, el_row ch799603el.r43 rfl rfl rfl,
    el_row ch799603el.r44 rfl rfl rfl, el_row ch799603el.r45 rfl rfl rfl,
    el_row ch799603el.r46 rfl rfl rfl, el_row ch799603el.r47 rfl rfl rfl,
    el_row ch799603el.r48 rfl rfl rfl, el_row ch799603el.r49 rfl rfl rfl,
    el_row ch799603el.r50 rfl rfl rfl, el_row ch799603el.r51 rfl rfl rfl,
    el_row ch799603el.r52 rfl rfl rfl, el_row ch799603el.r53 rfl rfl rfl,
    el_row ch799603el.r54 rfl rfl rfl, el_row ch799603el.r55 rfl rfl rfl,
    el_row ch799603el.r56 rfl rfl rfl, el_row ch799603el.r57 rfl rfl rfl,
    el_row ch799603el.r58 rfl rfl rfl, el_row ch799603el.r59 rfl rfl rfl,
    el_row ch799603el.r60 rfl rfl rfl, el_row ch799603el.r61 rfl rfl rfl,
    el_row ch799603el.r62 rfl rfl rfl, el_row ch799603el.r63 rfl rfl rfl,
    el_row ch799603el.r64 rfl rfl rfl, el_row ch799603el.r65 rfl rfl rfl,
    el_row ch799603el.r66 rfl rfl rfl, el_row ch799603el.r67 rfl rfl rfl,
    el_row ch799603el.r68 rfl rfl rfl, el_row ch799603el.r69 rfl rfl rfl,
    el_row ch799603el.r70 rfl rfl rfl, el_row ch799603el.r71 rfl rfl rfl,
    el_row ch799603el.r72 rfl rfl rfl, el_row ch799603el.r73 rfl rfl rfl,
    el_row ch799603el.r74 rfl rfl rfl, el_row ch799603el.r75 rfl rfl rfl,
    el_row ch799603el.r76 rfl rfl rfl, el_row ch799603el.r77 rfl rfl rfl,
    el_row ch799603el.r78 rfl rfl rfl, el_row ch799603el.r79 rfl rfl rfl,
    el_row ch799603el.r80 rfl rfl rfl]

theorem ew_length : ew.length = 81 := by decide +kernel

theorem nil_mem_ew : ([] : List ℕ) ∈ ew := by decide +kernel

theorem ra_lt3 : ra.getD 0 0 < 81 ∧ ra.getD 1 0 < 81 ∧ ra.getD 2 0 < 81 := by decide +kernel

theorem mem_ew {w : List ℕ} (hw : w ∈ ew) : ∃ i < 81, ew.getD i [] = w := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hw
  exact ⟨i, by rw [← ew_length]; exact hi, List.getD_eq_getElem _ _ hi⟩

theorem pairwise_of_incB : ∀ {l : List ℕ}, incB l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have h' : (Nat.blt a b && incB (b :: l)) = true := h
    rw [Bool.and_eq_true, Nat.blt_eq] at h'
    have hbl := pairwise_of_incB h'.2
    refine List.Pairwise.cons (fun c hc => ?_) hbl
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h'.1
    · exact h'.1.trans (List.rel_of_pairwise_cons hbl hc)

theorem es_inj {i j : ℕ} (hi : i < 81) (hj : j < 81)
    (h : es.getD i 0 % 2 ^ 2704 = es.getD j 0 % 2 ^ 2704) : i = j := by
  have hl := es_length
  have hlt : ∀ m < 81, es.getD m 0 < 2 ^ 2704 := fun m hm => by
    rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hm)]
    exact blt_lt (List.all_eq_true.1 es_lt _ (List.getElem_mem _))
  have hi' : i < es.length := by rw [hl]; exact hi
  have hj' : j < es.length := by rw [hl]; exact hj
  rw [Nat.mod_eq_of_lt (hlt i hi), Nat.mod_eq_of_lt (hlt j hj),
    List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj'] at h
  have hp := List.pairwise_iff_getElem.1 (pairwise_of_incB inc_ok)
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (Nat.ne_of_lt (hp i j hi' hj' h'))
  · exact absurd h.symm (Nat.ne_of_lt (hp j i hj' hi' h'))

noncomputable def D3 : Subgroup F42C := Subgroup.closure (gD '' {k | k < 4})

theorem D3_spec : (∀ x : F42C, x ∈ D3 ↔ ∃ w ∈ ew, wordElt gD w = x) ∧ Nat.card D3 = ew.length := by
  have : Finite F42C := finite_adjF
  refine enum_spec (fun w hw => ?_) nil_mem_ew (fun w hw k hk => ?_) ?_
  · obtain ⟨i, hi, rfl⟩ := mem_ew hw
    exact (el_all i hi).1
  · obtain ⟨i, hi, rfl⟩ := mem_ew hw
    obtain ⟨-, -, hm⟩ := el_all i hi
    obtain ⟨hn, hb⟩ := hm k hk
    refine ⟨ew.getD (nx.getD (4 * i + k) 0) [], ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [ew_length]; exact hn)]
      exact List.getElem_mem _
    · exact ((el_all _ hn).2.1.eq_iff hb).2 rfl
  · rw [List.Nodup, List.pairwise_iff_getElem]
    intro i j hi hj hij heq
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at heq
    have hi' : i < 81 := by rw [← ew_length]; exact hi
    have hj' : j < 81 := by rw [← ew_length]; exact hj
    have ei : eE i = wordElt gD ew[i] := congrArg (wordElt gD) (List.getD_eq_getElem _ _ hi)
    have ej : eE j = wordElt gD ew[j] := congrArg (wordElt gD) (List.getD_eq_getElem _ _ hj)
    have heq' : eE i = eE j := by rw [ei, ej]; exact heq
    exact Nat.ne_of_lt hij (es_inj hi' hj' (((el_all i hi').2.1.eq_iff (el_all j hj').2.1).1 heq'))

theorem D3_le : D3 ≤ Lv2 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact (gD_spec hk).1

theorem factorization_three_sp6' : (1451520 : ℕ).factorization 3 = 4 := by
  have h : (1451520 : ℕ) = 3 ^ 4 * 17920 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem D3_sylow : IsSylowOf 3 D3 (Lv2) := by
  have : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine isSylowOf_of_card_p D3_le ?_
  rw [D3_spec.2, ew_length, card_Lv2, factorization_three_sp6']
  norm_num

noncomputable abbrev rep (j : ℕ) : F42C := eE (ra.getD j 0)

theorem card_u26' : Fintype.card {p : Fin 52 // CFSG.KD.F4Inv.u26.testBit p = true} = 26 := by
  decide +kernel

theorem rep0_not : ¬IsConj rAE (rep 0) := by
  have eA : endo rAE = toEnd (ZMod 2) rAB := hasBits_rAE
  have e0 : endo (rep 0) = toEnd (ZMod 2) (es.getD (ra.getD 0 0) 0) := (el_all _ ra_lt3.1).2.1
  have hAU : 14 ≤ finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1) ⊓
      coordSub (ZMod 2) CFSG.KD.F4Inv.u26) := by
    have h := fixSubChk_sound (K := ZMod 2) CFSG.KD.F4Inv.kRAU_ok
    rw [sBits_three, ← eA] at h
    exact h
  have h0U : finrank (ZMod 2) ↥(LinearMap.ker (endo (rep 0) - 1) ⊓
      coordSub (ZMod 2) CFSG.KD.F4Inv.u26) ≤ 8 := by
    have h := rankSubChk_sound (K := ZMod 2) k0_ok
    rw [← e0] at h
    have h2 := finrank_map_add_finrank_ker_inf (endo (rep 0) - 1)
      (coordSub (ZMod 2) CFSG.KD.F4Inv.u26)
    have h3 := finrank_coordSub_le (K := ZMod 2) CFSG.KD.F4Inv.u26
    rw [card_u26'] at h3
    have hl := k0_length.1
    omega
  intro h
  have e : finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1) ⊓
      coordSub (ZMod 2) CFSG.KD.F4Inv.u26) = finrank (ZMod 2) ↥(LinearMap.ker (endo (rep 0) - 1) ⊓
      coordSub (ZMod 2) CFSG.KD.F4Inv.u26) := finrank_ker_inf_eq_of_isConj u26_invariant h
  omega

theorem rep2_not : ¬IsConj rAE (rep 2) := by
  have eA : endo rAE = toEnd (ZMod 2) rAB := hasBits_rAE
  have e2 : endo (rep 2) = toEnd (ZMod 2) (es.getD (ra.getD 2 0) 0) :=
    (el_all _ ra_lt3.2.2).2.1
  have hA : 22 ≤ finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1)) := by
    have h := fixChk_sound (K := ZMod 2) CFSG.KD.F4Inv.kRA_ok
    rw [sBits_three, ← eA] at h
    exact h
  have h2 : finrank (ZMod 2) ↥(LinearMap.ker (endo (rep 2) - 1)) ≤ 16 := by
    have h := rankChk_sound (K := ZMod 2) k2_ok
    rw [← e2] at h
    have h' := finrank_range_add_finrank_ker_F4 (K := ZMod 2) (endo (rep 2) - 1)
    have hl := k0_length.2
    omega
  intro h
  have e : finrank (ZMod 2) ↥(LinearMap.ker (endo rAE - 1)) =
      finrank (ZMod 2) ↥(LinearMap.ker (endo (rep 2) - 1)) := finrank_ker_eq_of_isConj h
  omega

theorem cv_row {i n : ℕ} (h : (cvN es cw cl ri ra i == n) = true) (hn : n = 1) {j : ℕ}
    (hj : i = j) : eqS (saltOf (es.getD j 0)) oneS = true ∨
      eqS (mulS (mulS (saltOf (es.getD j 0)) (saltOf (es.getD j 0))) (saltOf (es.getD j 0)))
        oneS = false ∨
      (ri.getD j 0 < 3 ∧ lvOK (cw.getD j 0) (cl.getD j 0) = true ∧
        eqS (mulS (wordS (cw.getD j 0) (cl.getD j 0)) (saltOf (es.getD j 0)))
          (mulS (saltOf (es.getD (ra.getD (ri.getD j 0) 0) 0))
            (wordS (cw.getD j 0) (cl.getD j 0))) = true) := by
  subst hn hj
  have h := beq_iff_eq.1 h
  unfold cvN at h
  rw [strictN_eq] at h
  by_cases h1 : (eqS (saltOf (es.getD i 0)) oneS || !eqS (mulS (mulS (saltOf (es.getD i 0))
      (saltOf (es.getD i 0))) (saltOf (es.getD i 0))) oneS) = true
  · rw [Bool.or_eq_true] at h1
    rcases h1 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl (by simpa using h1))
  · rw [if_neg h1, strictN_eq] at h
    have h2' := toNat_eq_one (Nat.eq_one_of_mul_eq_one_right h)
    rw [Bool.and_eq_true, Nat.blt_eq] at h2'
    exact Or.inr (Or.inr ⟨h2'.1, h2'.2, toNat_eq_one (Nat.eq_one_of_mul_eq_one_left h)⟩)

theorem cv_all : ∀ i < 81, eqS (saltOf (es.getD i 0)) oneS = true ∨
      eqS (mulS (mulS (saltOf (es.getD i 0)) (saltOf (es.getD i 0))) (saltOf (es.getD i 0)))
        oneS = false ∨
      (ri.getD i 0 < 3 ∧ lvOK (cw.getD i 0) (cl.getD i 0) = true ∧
        eqS (mulS (wordS (cw.getD i 0) (cl.getD i 0)) (saltOf (es.getD i 0)))
          (mulS (saltOf (es.getD (ra.getD (ri.getD i 0) 0) 0))
            (wordS (cw.getD i 0) (cl.getD i 0))) = true) := by
  intro i hi
  interval_cases i
  exacts [cv_row ch799603cv.r0 rfl rfl, cv_row ch799603cv.r1 rfl rfl, cv_row ch799603cv.r2 rfl rfl,
    cv_row ch799603cv.r3 rfl rfl, cv_row ch799603cv.r4 rfl rfl, cv_row ch799603cv.r5 rfl rfl,
    cv_row ch799603cv.r6 rfl rfl, cv_row ch799603cv.r7 rfl rfl, cv_row ch799603cv.r8 rfl rfl,
    cv_row ch799603cv.r9 rfl rfl, cv_row ch799603cv.r10 rfl rfl, cv_row ch799603cv.r11 rfl rfl,
    cv_row ch799603cv.r12 rfl rfl, cv_row ch799603cv.r13 rfl rfl, cv_row ch799603cv.r14 rfl rfl,
    cv_row ch799603cv.r15 rfl rfl, cv_row ch799603cv.r16 rfl rfl, cv_row ch799603cv.r17 rfl rfl,
    cv_row ch799603cv.r18 rfl rfl, cv_row ch799603cv.r19 rfl rfl, cv_row ch799603cv.r20 rfl rfl,
    cv_row ch799603cv.r21 rfl rfl, cv_row ch799603cv.r22 rfl rfl, cv_row ch799603cv.r23 rfl rfl,
    cv_row ch799603cv.r24 rfl rfl, cv_row ch799603cv.r25 rfl rfl, cv_row ch799603cv.r26 rfl rfl,
    cv_row ch799603cv.r27 rfl rfl, cv_row ch799603cv.r28 rfl rfl, cv_row ch799603cv.r29 rfl rfl,
    cv_row ch799603cv.r30 rfl rfl, cv_row ch799603cv.r31 rfl rfl, cv_row ch799603cv.r32 rfl rfl,
    cv_row ch799603cv.r33 rfl rfl, cv_row ch799603cv.r34 rfl rfl, cv_row ch799603cv.r35 rfl rfl,
    cv_row ch799603cv.r36 rfl rfl, cv_row ch799603cv.r37 rfl rfl, cv_row ch799603cv.r38 rfl rfl,
    cv_row ch799603cv.r39 rfl rfl, cv_row ch799603cv.r40 rfl rfl, cv_row ch799603cv.r41 rfl rfl,
    cv_row ch799603cv.r42 rfl rfl, cv_row ch799603cv.r43 rfl rfl, cv_row ch799603cv.r44 rfl rfl,
    cv_row ch799603cv.r45 rfl rfl, cv_row ch799603cv.r46 rfl rfl, cv_row ch799603cv.r47 rfl rfl,
    cv_row ch799603cv.r48 rfl rfl, cv_row ch799603cv.r49 rfl rfl, cv_row ch799603cv.r50 rfl rfl,
    cv_row ch799603cv.r51 rfl rfl, cv_row ch799603cv.r52 rfl rfl, cv_row ch799603cv.r53 rfl rfl,
    cv_row ch799603cv.r54 rfl rfl, cv_row ch799603cv.r55 rfl rfl, cv_row ch799603cv.r56 rfl rfl,
    cv_row ch799603cv.r57 rfl rfl, cv_row ch799603cv.r58 rfl rfl, cv_row ch799603cv.r59 rfl rfl,
    cv_row ch799603cv.r60 rfl rfl, cv_row ch799603cv.r61 rfl rfl, cv_row ch799603cv.r62 rfl rfl,
    cv_row ch799603cv.r63 rfl rfl, cv_row ch799603cv.r64 rfl rfl, cv_row ch799603cv.r65 rfl rfl,
    cv_row ch799603cv.r66 rfl rfl, cv_row ch799603cv.r67 rfl rfl, cv_row ch799603cv.r68 rfl rfl,
    cv_row ch799603cv.r69 rfl rfl, cv_row ch799603cv.r70 rfl rfl, cv_row ch799603cv.r71 rfl rfl,
    cv_row ch799603cv.r72 rfl rfl, cv_row ch799603cv.r73 rfl rfl, cv_row ch799603cv.r74 rfl rfl,
    cv_row ch799603cv.r75 rfl rfl, cv_row ch799603cv.r76 rfl rfl, cv_row ch799603cv.r77 rfl rfl,
    cv_row ch799603cv.r78 rfl rfl, cv_row ch799603cv.r79 rfl rfl, cv_row ch799603cv.r80 rfl rfl]

theorem key_kc {x : F42C} (hxL : x ∈ Lv2) (hx : IsConj rAE x) :
    ∃ l ∈ Lv2, l * x * l⁻¹ = rep 1 := by
  have : Finite F42C := finite_adjF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 hx
  have hr3 : rAE ^ 3 = 1 := nodeElt_pow_three (K := ZMod 2)
  have hr1 : rAE ≠ 1 := nodeElt_ne_one (K := ZMod 2)
  have hx3 : x ^ 3 = 1 := by rw [← hc₀, conj_pow, hr3]; simp
  have hx1 : x ≠ 1 := fun h => hr1 (conj_eq_one_iff.1 (hc₀.trans h))
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]; norm_num)
  obtain ⟨k, hkL, hk⟩ := exists_conj_le_sylowOf_p D3_sylow (Subgroup.zpowers_le.2 hxL) hxp
  obtain ⟨w, hw, hwe⟩ := (D3_spec.1 _).1 (hk x (Subgroup.mem_zpowers x))
  obtain ⟨i, hi, rfl⟩ := mem_ew hw
  have hy : eE i = k * x * k⁻¹ := hwe
  have hy3 : eE i * eE i * eE i = 1 := by
    rw [← pow_three', hy, conj_pow, hx3]
    simp
  have hy1 : eE i ≠ 1 := fun h => hx1 (conj_eq_one_iff.1 (hy.symm.trans h))
  have hbS := hasBitsS_saltOf (el_all i hi).2.1
  rcases cv_all i hi with h | h | ⟨hr, hw', hc⟩
  · exact absurd ((hbS.eq_iff hasBitsS_one).2 h) hy1
  · rw [((hbS.mul hbS).mul hbS).eq_iff hasBitsS_one |>.1 hy3] at h
    exact absurd h (by decide)
  · have hrl : ra.getD (ri.getD i 0) 0 < 81 := by
      rcases (by omega : ri.getD i 0 = 0 ∨ ri.getD i 0 = 1 ∨ ri.getD i 0 = 2) with e | e | e <;>
        rw [e]
      exacts [ra_lt3.1, ra_lt3.2.1, ra_lt3.2.2]
    have hR := hasBitsS_saltOf (el_all _ hrl).2.1
    have hW := hasBitsS_wordS (K := ZMod 2) (cw.getD i 0) (cl.getD i 0)
    have hCe : wE (cw.getD i 0) (cl.getD i 0) * eE i =
        rep (ri.getD i 0) * wE (cw.getD i 0) (cl.getD i 0) :=
      ((hW.mul hbS).eq_iff (hR.mul hW)).2 hc
    set C := wE (cw.getD i 0) (cl.getD i 0) with hC
    have hCL : C ∈ Lv2 := wE_mem _ _ hw'
    have hconj : (C * k) * x * (C * k)⁻¹ = rep (ri.getD i 0) := by
      have e1 : (C * k) * x * (C * k)⁻¹ = C * eE i * C⁻¹ := by rw [hy]; group
      rw [e1, hCe, mul_inv_cancel_right]
    have hAR : IsConj rAE (rep (ri.getD i 0)) := hx.trans (isConj_iff.2 ⟨C * k, hconj⟩)
    have h1 : ri.getD i 0 = 1 := by
      rcases (by omega : ri.getD i 0 = 0 ∨ ri.getD i 0 = 1 ∨ ri.getD i 0 = 2) with e | e | e
      · rw [e] at hAR
        exact absurd hAR rep0_not
      · exact e
      · rw [e] at hAR
        exact absurd hAR rep2_not
    rw [h1] at hconj
    exact ⟨C * k, mul_mem hCL hkL, hconj⟩

theorem fusion_kc : ∀ x₁ ∈ Lv2, ∀ x₂ ∈ Lv2, IsConj rAE x₁ →
    IsConj rAE x₂ → ∃ l ∈ Lv2, l * x₁ * l⁻¹ = x₂ := by
  intro x₁ h₁ x₂ h₂ hx₁ hx₂
  obtain ⟨l₁, hl₁, e₁⟩ := key_kc h₁ hx₁
  obtain ⟨l₂, hl₂, e₂⟩ := key_kc h₂ hx₂
  refine ⟨l₂⁻¹ * l₁, mul_mem (inv_mem hl₂) hl₁, ?_⟩
  have : l₂⁻¹ * l₁ * x₁ * (l₂⁻¹ * l₁)⁻¹ = l₂⁻¹ * (l₁ * x₁ * l₁⁻¹) * l₂ := by group
  rw [this, e₁, ← e₂]
  group

end CFSG.KC.F4Levi

end
