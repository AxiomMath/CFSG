module

public import Certificates.Kernel.Sp43K.GlueFacts
public import Certificates.Kernel.Sp43K.OrbA
public import Certificates.Kernel.Sp43K.OrbB
public import Certificates.Kernel.Sp43K.Cases
public import CFSG.Certificates.Kernel.Sp43KOrbGrp
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Certificates.Kernel.Sp43KOrbSound
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Classes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.KD.Sp43K

open CFSG.KC.Sp43K CFSG.Sp43 Subgroup

@[expose] noncomputable def xR (i r : ℕ) : G := ofT (fldT (xP i) r)

theorem caseC_all : ∀ j < 63, caseC j = true := by
  intro j hj
  interval_cases j
  exacts [ch1322001c_0, ch1322001c_1, ch1322001c_2, ch1322001c_3, ch1322001c_4, ch1322001c_5,
    ch1322001c_6, ch1322001c_7, ch1322001c_8, ch1322001c_9, ch1322001c_10, ch1322001c_11,
    ch1322001c_12, ch1322001c_13, ch1322001c_14, ch1322001c_15, ch1322001c_16, ch1322001c_17,
    ch1322001c_18, ch1322001c_19, ch1322001c_20, ch1322001c_21, ch1322001c_22, ch1322001c_23,
    ch1322001c_24, ch1322001c_25, ch1322001c_26, ch1322001c_27, ch1322001c_28, ch1322001c_29,
    ch1322001c_30, ch1322001c_31, ch1322001c_32, ch1322001c_33, ch1322001c_34, ch1322001c_35,
    ch1322001c_36, ch1322001c_37, ch1322001c_38, ch1322001c_39, ch1322001c_40, ch1322001c_41,
    ch1322001c_42, ch1322001c_43, ch1322001c_44, ch1322001c_45, ch1322001c_46, ch1322001c_47,
    ch1322001c_48, ch1322001c_49, ch1322001c_50, ch1322001c_51, ch1322001c_52, ch1322001c_53,
    ch1322001c_54, ch1322001c_55, ch1322001c_56, ch1322001c_57, ch1322001c_58, ch1322001c_59,
    ch1322001c_60, ch1322001c_61, ch1322001c_62]

theorem ncsC_all : ∀ i < 5, ncsC i = true := by
  intro i hi
  interval_cases i
  exacts [ch1322001r_0, ch1322001r_1, ch1322001r_2, ch1322001r_3, ch1322001r_4]

private theorem cjobs_cover : ∀ i < 5, ∀ k < (ncs.getD i 0 + 7) / 8,
    ∃ j < 63, cjobs.getD j (0, 0) = (i, 8 * k) := by
  decide

theorem casesOK_spec {i : ℕ} :
    ∀ (L : List CaseT), casesOK i L = true → ∀ m < L.length, caseOne i (L.getD m default) = true
  | [], _ => fun m hm => by simp at hm
  | c :: L, h => by
    have h' : (caseOne i c && casesOK i L) = true := h
    simp only [Bool.and_eq_true] at h'
    intro m hm
    rcases m with _ | m
    · exact h'.1
    · rw [List.getD_cons_succ]
      exact casesOK_spec L h'.2 m (by simpa using hm)

theorem ncsC_spec {i : ℕ} (hi : i < 5) : (cs i).length = ncs.getD i 0 ∧
    nr.getD i 0 = ncs.getD i 0 ∧ ∀ r < ncs.getD i 0, fldT (xP i) r = ((cs i).getD r default).1 := by
  have h := ncsC_all i hi
  unfold ncsC at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem caseOne_all {i : ℕ} (hi : i < 5) :
    ∀ r < ncs.getD i 0, caseOne i ((cs i).getD r default) = true := by
  intro r hr
  obtain ⟨j, hj, e⟩ := cjobs_cover i hi (r / 8) (by omega)
  have h := caseC_all j hj
  unfold caseC at h
  rw [e] at h
  dsimp only at h
  have hlen := (ncsC_spec hi).1
  have := casesOK_spec _ h (r - 8 * (r / 8)) (by
    rw [List.length_take, List.length_drop]
    omega)
  rwa [getD_chunk _ _ (Nat.mul_div_le r 8) (by omega)] at this

theorem spC_cases {i : ℕ} (hi : i < 5) :
    ∀ c ∈ cs i, spT c.1 = true ∧ spT c.2.2.1 = true ∧ spT c.2.2.2.1 = true := by
  have h := (spC_spec (spC_all i hi)).2.2.2.2.2.2
  generalize cs i = L at h ⊢
  induction L with
  | nil => intro c hc; simp at hc
  | cons c L ih =>
    have h' : (spT c.1 && spT c.2.2.1 && spT c.2.2.2.1 &&
        List.rec (motive := fun _ => Bool) true
          (fun c _ ih => spT c.1 && spT c.2.2.1 && spT c.2.2.2.1 && ih) L) = true := h
    simp only [Bool.and_eq_true] at h'
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2⟩
    · exact ih h'.2 d hd

theorem inG_hAB {j : ℕ} (hj : j < 6) : InG (hA j) ∧ InG (hB j) := by
  by_cases h5 : j < 5
  · rw [hA, hB, if_pos h5, if_pos h5]
    exact ⟨(lst_member h5).1, (lst_member h5).2.1⟩
  · rw [hA, hB, if_neg h5, if_neg h5]
    exact ⟨inG_G5.1, inG_G5.2.1⟩

theorem case_spec {i : ℕ} (hi : i < 5) {r : ℕ} (hr : r < nr.getD i 0) :
    ∃ j < 6, ∃ g : G, Mk i ⊔ zpowers (xR i r) = (Mk j).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨hlen, hnr, hx⟩ := ncsC_spec hi
  rw [hnr] at hr
  have hc := caseOne_all hi r hr
  have hmem : (cs i).getD r default ∈ cs i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  have hxr := hx r hr
  generalize (cs i).getD r default = c at hc hmem hxr
  obtain ⟨s1, s2, s3⟩ := spC_cases hi c hmem
  unfold caseOne caseK at hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ox, og⟩, og'⟩, hgg⟩, hj⟩, hw1⟩, hw2⟩, hmem5⟩, e1⟩, e2⟩ := hc
  have hxG := inG_of_spT ox s1
  have hgG := inG_of_spT og s2
  have hg'G := inG_of_spT og' s3
  obtain ⟨ha, hb, -⟩ := lst_member hi
  obtain ⟨hh1, hh2⟩ := inG_hAB hj
  have hsub : ∀ {k : ℕ}, InG k → (c.2.1 = 5 ∨ ∃ q < ords.getD c.2.1 0,
      fldT (mP c.2.1) q = conjT c.2.2.1 c.2.2.2.1 k) →
      ofT (conjT c.2.2.1 c.2.2.2.1 k) ∈ sub2T (hA c.2.1) (hB c.2.1) := by
    intro k hk h
    rw [← Mk]
    rcases h with h | ⟨q, hq, e⟩
    · rw [h, mk_five]
      exact Subgroup.mem_top _
    · by_cases h5 : c.2.1 < 5
      · exact mem_mk_of_fld h5 hq e
      · have : c.2.1 = 5 := by omega
        rw [this, mk_five]
        exact Subgroup.mem_top _
  have hjoin := case_join (a := gA i) (b := gB i) ha hb hxG hgG hg'G hh1 hh2 hgg
    (hsub ha (by
      rcases hmem5 with h | ⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, h1, h2⟩))
    (hsub hb (by
      rcases hmem5 with h | ⟨⟨⟨⟨⟨-, -⟩, h1⟩, h2⟩, -⟩, -⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, h1, h2⟩))
    (hsub hxG (by
      rcases hmem5 with h | ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h1⟩, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨_, h1, h2⟩))
    hw1 hw2 e1 e2
  refine ⟨c.2.1, hj, (ofT c.2.2.1)⁻¹, ?_⟩
  rw [mk_lt hi, xR, hxr, Mk]
  exact hjoin

theorem inG_xP {i : ℕ} (hi : i < 5) : ∀ r < nr.getD i 0, InG (fldT (xP i) r) := by
  intro r hr
  obtain ⟨hlen, hnr, hx⟩ := ncsC_spec hi
  rw [hnr] at hr
  have hc := caseOne_all hi r hr
  have hmem : (cs i).getD r default ∈ cs i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _
  rw [hx r hr]
  generalize (cs i).getD r default = c at hc hmem
  unfold caseOne caseK at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨ox, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hc
  exact inG_of_spT ox (spC_cases hi c hmem).1

theorem nT_eq : nT = 6560 := rfl

theorem orbC_all : ∀ j < 50, orbC j = true := by
  intro j hj
  interval_cases j
  exacts [ch1322001o_0, ch1322001o_1, ch1322001o_2, ch1322001o_3, ch1322001o_4, ch1322001o_5,
    ch1322001o_6, ch1322001o_7, ch1322001o_8, ch1322001o_9, ch1322001o_10, ch1322001o_11,
    ch1322001o_12, ch1322001o_13, ch1322001o_14, ch1322001o_15, ch1322001o_16, ch1322001o_17,
    ch1322001o_18, ch1322001o_19, ch1322001o_20, ch1322001o_21, ch1322001o_22, ch1322001o_23,
    ch1322001o_24, ch1322001o_25, ch1322001o_26, ch1322001o_27, ch1322001o_28, ch1322001o_29,
    ch1322001o_30, ch1322001o_31, ch1322001o_32, ch1322001o_33, ch1322001o_34, ch1322001o_35,
    ch1322001o_36, ch1322001o_37, ch1322001o_38, ch1322001o_39, ch1322001o_40, ch1322001o_41,
    ch1322001o_42, ch1322001o_43, ch1322001o_44, ch1322001o_45, ch1322001o_46, ch1322001o_47,
    ch1322001o_48, ch1322001o_49]

theorem oOne_all {i : ℕ} (hi : i < 5) : ∀ t < nT,
    oOne (nsI i).1.1 (nsI i).1.2 (nsI i).2.1 (nsI i).2.2 (ords.getD i 0) (mP i) (nr.getD i 0)
      (xP i) nT TP (oD i) t ((oR i).getD t (0, 0)) = true := by
  intro t ht
  rw [nT_eq] at ht
  have h := orbC_all (10 * i + t / 656) (by omega)
  unfold orbC orbPart at h
  have e1 : (10 * i + t / 656) / 10 = i := by omega
  have e2 : (10 * i + t / 656) % 10 = t / 656 := by omega
  rw [e1, e2] at h
  dsimp only at h
  have hs : 656 * (t / 656) ≤ t := Nat.mul_div_le t 656
  have := ((oGo_spec _ _ h).2 t hs (by rw [nT_eq]; omega)).2
  rwa [getD_chunk _ _ hs (by omega)] at this

theorem orb_member {i : ℕ} (hi : i < 5) : ∀ t < nT, InG (fldT TP t) ∧
    (fldT (oD i) t = 0 → ofT (fldT TP t) ∈ Mk i) ∧
    (1 ≤ fldT (oD i) t → ∃ rr < nr.getD i 0, ∃ n ∈ normalizer (Mk i : Set G),
      ofT (fldT TP t) = n * xR i rr * n⁻¹) := by
  intro t ht
  obtain ⟨n1, n2, n3, n4, e1, e2, -⟩ := normC_spec hi
  have hM : ∀ x < ords.getD i 0, InG (fldT (mP i) x) ∧ ofT (fldT (mP i) x) ∈ Mk i :=
    fun x hx => ⟨(inG_of_fld hi hx rfl).2, mem_mk_of_fld hi hx rfl⟩
  obtain ⟨h1, h2, h3⟩ := orb_spec (H := Mk i) (oOne_all hi) hM (inG_xP hi) n1 n2 n3 n4 e1 e2 t ht
  refine ⟨h1, h2, fun hd => ?_⟩
  obtain ⟨rr, hrr, n, hn, e⟩ := h3 hd
  exact ⟨rr, hrr, n, normGens_le hi hn, e⟩

theorem tC_all : ∀ j < 10, tC j = true := by
  intro j hj
  interval_cases j
  exacts [ch1322001t_0, ch1322001t_1, ch1322001t_2, ch1322001t_3, ch1322001t_4, ch1322001t_5,
    ch1322001t_6, ch1322001t_7, ch1322001t_8, ch1322001t_9]

theorem tOne_all : ∀ t < nT,
    tOne G5.1 G5.2.1 G5.2.2.1 G5.2.2.2 nT TP t (TQ.getD t (0, 0)) = true := by
  intro t ht
  rw [nT_eq] at ht
  have h := tC_all (t / 656) (by omega)
  unfold tC at h
  dsimp only at h
  have hs : 656 * (t / 656) ≤ t := Nat.mul_div_le t 656
  have := ((tGo_spec _ _ h).2 t hs (by rw [nT_eq]; omega)).2
  rwa [getD_chunk _ _ hs (by omega)] at this

@[expose] def tSet : Set G := {g | ∃ t < nT, ofT (fldT TP t) = g}

theorem tSet_conj_a : ∀ s ∈ tSet, ofT G5.1 * s * (ofT G5.1)⁻¹ ∈ tSet := by
  rintro _ ⟨t, ht, rfl⟩
  have h := tOne_all t ht
  unfold tOne at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hq1⟩, e1⟩, -⟩, -⟩ := h
  obtain ⟨g1, -, g3, -⟩ := inG_G5
  obtain ⟨-, -, -, -, m1, -⟩ := g5C_spec
  refine ⟨_, hq1, ?_⟩
  rw [e1, ofT_conjT g1 g3 (orb_member (i := 0) (by norm_num) t ht).1 m1]

theorem tSet_conj_b : ∀ s ∈ tSet, ofT G5.2.1 * s * (ofT G5.2.1)⁻¹ ∈ tSet := by
  rintro _ ⟨t, ht, rfl⟩
  have h := tOne_all t ht
  unfold tOne at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hq2⟩, e2⟩ := h
  obtain ⟨-, g2, -, g4⟩ := inG_G5
  obtain ⟨-, -, -, -, -, m2⟩ := g5C_spec
  refine ⟨_, hq2, ?_⟩
  rw [e2, ofT_conjT g2 g4 (orb_member (i := 0) (by norm_num) t ht).1 m2]

theorem tSet_conj : ∀ g : G, ∀ s ∈ tSet, g * s * g⁻¹ ∈ tSet := by
  intro g
  have hg : g ∈ Subgroup.closure ({ofT G5.1, ofT G5.2.1} : Set G) := by
    have : g ∈ Mk 5 := by rw [mk_five]; exact Subgroup.mem_top g
    rwa [mk_five_eq] at this
  exact conj_closed tSet tSet_conj_a tSet_conj_b g hg

theorem p0_tSet {z : G} (hz : z ∈ sub2T p0.1 p0.2) (hz1 : z ≠ 1) : z ∈ tSet := by
  obtain ⟨t, ht, rfl⟩ := (lst_p0.2.2.2.2.1 z).1 hz
  obtain ⟨-, hlen, hin⟩ := p0C_spec
  rcases inGo_spec p0T 0 hin t (Nat.zero_le t) (by rw [hlen]; omega) with h | ⟨hx, e⟩
  · rw [h, ofT_oneT] at hz1
    exact absurd rfl hz1
  · exact ⟨_, hx, by rw [e]⟩

theorem three_mem {y : G} {k : ℕ} (hy : orderOf y = 3 ^ k) (hy1 : y ≠ 1) : y ∈ tSet := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P₀, hP₀⟩ := sylow3
  have hyP : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hy])
  obtain ⟨S, hS⟩ := hyP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ S
  have hyS : y ∈ (S : Subgroup G) := hS (Subgroup.mem_zpowers y)
  rw [← hg, CFSG.Sp43.mem_smul_sylow_iff] at hyS
  rw [hP₀] at hyS
  have hz1 : g⁻¹ * y * g ≠ 1 := by
    intro h
    apply hy1
    have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    rw [this, h]
    group
  have := tSet_conj g _ (p0_tSet hyS hz1)
  have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
  rwa [e] at this

theorem exists_rep {i : ℕ} (hi : i < 5) (y : G) (hy : ∃ k, orderOf y = 3 ^ k) (hy1 : y ≠ 1) :
    y ∈ Mk i ∨ ∃ r < nr.getD i 0, ∃ n ∈ normalizer (Mk i : Set G), y = n * xR i r * n⁻¹ := by
  obtain ⟨k, hk⟩ := hy
  obtain ⟨t, ht, rfl⟩ := three_mem hk hy1
  obtain ⟨-, h0, h1⟩ := orb_member hi t ht
  rcases Nat.eq_zero_or_pos (fldT (oD i) t) with hd | hd
  · exact Or.inl (h0 hd)
  · exact Or.inr (h1 hd)

end CFSG.KD.Sp43K

end
