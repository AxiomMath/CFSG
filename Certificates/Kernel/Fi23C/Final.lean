module

public import Certificates.Kernel.Fi23C.Group
public import Certificates.Kernel.Fi23C.Prop
public import Certificates.Kernel.Fi22Cent.Facts
public import Certificates.Kernel.Fi22Core.OrbData
public import CFSG.Sporadic.Fi22.Simple
public import CFSG.Sporadic.Th.CertificateChunks
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23C

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KS.Raw.Orb
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CertificateChecks.KernelFi23M

theorem treeAct_rep {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)]
    {par lab al be D bi : Table} {x y r : G} (hal : CFSG.Sporadic.Th.Rep n al x)
    (hbe : CFSG.Sporadic.Th.Rep n be y) (hbi : CFSG.Sporadic.Th.Rep n bi y⁻¹)
    (hD : CFSG.Sporadic.Th.Rep n D r) (hx : x⁻¹ = x) (c : ℕ → G)
    (hc : ∀ k, c k = if 0 < k ∧ ap par k < k then
      (if ap lab k = 1 then x else y) * c (ap par k) * (if ap lab k = 1 then x else y)⁻¹ else r) :
    ∀ k, ∀ m < n, treeAct par lab al be D bi k m = CFSG.Sporadic.Th.idx n (c k) m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hm
    rw [treeAct.eq_def, hc k]
    by_cases h : 0 < k ∧ ap par k < k
    · rw [dite_eq_left h, ite_eq_left h]
      by_cases hl : ap lab k = 1
      · have hm' : ap al m < n := by rw [hal m hm]; exact CFSG.Sporadic.Th.idx_lt x hm
        rw [ite_eq_left (beq_iff_eq.2 hl), ite_eq_left hl, ih _ h.2 _ hm',
          hal _ (CFSG.Sporadic.Th.idx_lt _ hm'), hx, CFSG.Sporadic.Th.idx_mul,
          CFSG.Sporadic.Th.idx_mul, ← hal m hm]
      · have hm' : ap bi m < n := by rw [hbi m hm]; exact CFSG.Sporadic.Th.idx_lt _ hm
        rw [ite_eq_right (fun e => hl (beq_iff_eq.1 e)), ite_eq_right hl, ih _ h.2 _ hm',
          hbe _ (CFSG.Sporadic.Th.idx_lt _ hm'), CFSG.Sporadic.Th.idx_mul,
          CFSG.Sporadic.Th.idx_mul, ← hbi m hm]
    · rw [dite_eq_right h, ite_eq_right h]
      exact hD m hm

section Fi22

theorem fi22_conjPt_inv :
    ∀ k, (CFSG.Sporadic.Fi22.conjPt k)⁻¹ = CFSG.Sporadic.Fi22.conjPt k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [CFSG.Sporadic.Fi22.conjPt.eq_def]
    split_ifs with h
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, ih _ h.2, mul_assoc]
    · exact CFSG.Sporadic.Fi22.a_inv

theorem fi22_rep_bi :
    CFSG.Sporadic.Th.Rep 3510 (CFSG.Sporadic.Fi22.Native.genTables CFSG.Sporadic.Fi22.orb (-2))
      CFSG.Sporadic.Fi22.b⁻¹ := by
  have h := CFSG.Sporadic.Fi22.rep_gen (-2)
  have e : CFSG.Sporadic.Fi22.genG (-2) = CFSG.Sporadic.Fi22.b⁻¹ := by
    unfold CFSG.Sporadic.Fi22.genG
    simp only [show (-2 : ℤ) ≠ 1 by decide, show (-2 : ℤ) ≠ -1 by decide,
      show (-2 : ℤ) ≠ 2 by decide, ite_false]
  rw [e] at h
  exact h

theorem fi22_conjPt_eq (k : ℕ) :
    CFSG.Sporadic.Fi22.conjPt k = if 0 < k ∧ ap CFSG.Sporadic.Fi22.orb.par k < k then
      (if ap CFSG.Sporadic.Fi22.orb.lab k = 1 then CFSG.Sporadic.Fi22.a else CFSG.Sporadic.Fi22.b) *
        CFSG.Sporadic.Fi22.conjPt (ap CFSG.Sporadic.Fi22.orb.par k) *
        (if ap CFSG.Sporadic.Fi22.orb.lab k = 1 then CFSG.Sporadic.Fi22.a
          else CFSG.Sporadic.Fi22.b)⁻¹ else CFSG.Sporadic.Fi22.a := by
  rw [CFSG.Sporadic.Fi22.conjPt.eq_def]
  simp only [CFSG.Sporadic.Fi22.labG, dite_eq_ite]

theorem act22_idx : ∀ k, ∀ m < 3510,
    treeAct CFSG.Sporadic.Fi22.orb.par CFSG.Sporadic.Fi22.orb.lab CFSG.Sporadic.Fi22.orb.alpha
      CFSG.Sporadic.Fi22.orb.beta CFSG.Sporadic.Fi22.orb.alpha
      (CFSG.Sporadic.Fi22.Native.genTables CFSG.Sporadic.Fi22.orb (-2)) k m =
      CFSG.Sporadic.Th.idx 3510 (CFSG.Sporadic.Fi22.conjPt k) m :=
  treeAct_rep CFSG.Sporadic.Fi22.rep_alpha CFSG.Sporadic.Fi22.rep_beta fi22_rep_bi
    CFSG.Sporadic.Fi22.rep_alpha CFSG.Sporadic.Fi22.a_inv CFSG.Sporadic.Fi22.conjPt fi22_conjPt_eq

open CFSG.Sporadic.Fi22.Native CertificateChecks.KernelFi22Cent in
theorem treeAct_cTab : ∀ k, ∀ m < 3510,
    treeAct orbL.par orbL.lab orbL.alpha orbL.beta orbL.alpha
      (CFSG.Sporadic.Fi22.Native.genTables orbL (-2)) k m =
      ap (CFSG.Sporadic.Fi22.Native.cTab orbL (CFSG.Sporadic.Fi22.Native.genTables orbL (-2)) k) m := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m hm
    rw [treeAct.eq_def, CFSG.Sporadic.Fi22.Native.cTab.eq_def]
    by_cases h : 0 < k ∧ ap orbL.par k < k
    · rw [dite_eq_left h, dite_eq_left h]
      by_cases hl : (ap orbL.lab k == 1) = true
      · have hm' : ap orbL.alpha m < 3510 := by rw [ap_alpha]; exact gA_lt hm
        rw [if_pos hl, if_pos hl, ap_compT _ _ hm, ap_compT _ _ hm', ih _ h.2 _ hm']
      · have hm' : ap (CFSG.Sporadic.Fi22.Native.genTables orbL (-2)) m < 3510 := by
          rw [(bi_get hm).1]; exact (bi_get hm).2
        rw [if_neg hl, if_neg hl, ap_compT _ _ hm, ap_compT _ _ hm', ih _ h.2 _ hm']
    · rw [dite_eq_right h, dite_eq_right h]

theorem cK_idx {k m : ℕ} (hk : k < 3510) (hm : m < 3510) :
    CFSG.KS.Fi22Cent.cK k m = CFSG.Sporadic.Th.idx 3510 (CFSG.Sporadic.Fi22.conjPt k) m := by
  rw [← CertificateChecks.KernelFi22Cent.cTab_eq hk hm, ← treeAct_cTab k m hm, ← act22_idx k m hm]
  have e : CFSG.Sporadic.Fi22.orb = CFSG.Sporadic.Fi22.Native.orbL :=
    CertificateChecks.KernelFi22C.orbitData_eq
  rw [e]

end Fi22

section


theorem D_comm {i : ℕ} (hi : i < 3510) : phiX wD * cp (E i) = cp (E i) * phiX wD := by
  have h := cp_eqv wD (E_lt hi)
  have e : (phiX wD ⟨E i, E_lt hi⟩).val = E i := by rw [phiX_wD _ (E_lt hi)]; exact E_fix hi
  rw [e] at h
  calc phiX wD * cp (E i) = phiX wD * cp (E i) * (phiX wD)⁻¹ * phiX wD := by group
    _ = cp (E i) * phiX wD := by rw [← h]

theorem cp_fix0 {i : ℕ} (hi : i < 3510) : (cp (E i) ⟨0, hn⟩).val = 0 := by
  apply cp_inj (Fin.isLt _) (by norm_num)
  have h := cp_eqv (tt (E i)) (m := 0) (by norm_num)
  rw [h, cp_zero]
  change cp (E i) * phiX wD * (cp (E i))⁻¹ = phiX wD
  rw [← D_comm hi, mul_assoc, mul_inv_cancel, mul_one]

noncomputable abbrev cx (i j : ℕ) : ℕ := cJ G (E i) (E j)

theorem cx_cp {i j : ℕ} (hi : i < 3510) (hj : j < 3510) :
    cx i j = (cp (E i) ⟨E j, E_lt hj⟩).val := cJ_cp (E_lt hi) (E_lt hj)

theorem cx_star {i j : ℕ} (hi : i < 3510) (hj : j < 3510) :
    P (cx i j) < 3510 ∧ E (P (cx i j)) = cx i j := by
  have hx : cx i j < 31671 := cJ_lt (E_lt hi) (E_lt hj)
  rcases ep_facts hx with h | ⟨-, h0 | hD⟩
  · exact h
  · exfalso
    rw [cx_cp hi hj] at h0
    have e : cp (E i) ⟨E j, E_lt hj⟩ = cp (E i) ⟨0, hn⟩ := Fin.ext (by rw [h0, cp_fix0 hi])
    have := congrArg Fin.val ((cp (E i)).injective e)
    exact E_ne hj this
  · exfalso
    apply hD
    rw [cx_cp hi hj, ← phiX_wD _ (Fin.isLt _)]
    have e := congrArg (fun p : Equiv.Perm (Fin 31671) => (p ⟨E j, E_lt hj⟩).val) (D_comm hi)
    simp only [Equiv.Perm.mul_apply] at e
    rw [Fin.eta, e]
    have hf : phiX wD ⟨E j, E_lt hj⟩ = ⟨E j, E_lt hj⟩ := Fin.ext (by rw [phiX_wD _ (E_lt hj)]; exact E_fix hj)
    rw [hf]

theorem cx_conj {i j : ℕ} (hi : i < 3510) (hj : j < 3510) :
    cp (E (P (cx i j))) = cp (E i) * cp (E j) * (cp (E i))⁻¹ := by
  rw [(cx_star hi hj).2, cx_cp hi hj]
  exact cp_eqv (tt (E i)) (E_lt hj)

theorem prop_hyp :
    PropHyp 3510 7 (fun i => cp (E i)) (fun i => CFSG.Sporadic.Fi22.conjPt (Φ i))
      (fun i j => P (cx i j)) GS ORK OIK TP TG where
  o_lt i hi j hj := (cx_star hi hj).1
  o_eq i hi j hj := cx_conj hi hj
  X_inj i hi j hj h := E_inj hi hj (cp_inj (E_lt hi) (E_lt hj) h)
  X_inv i _ := cp_inv _
  Y_inv i _ := fi22_conjPt_inv _
  gs_lt s hs := (row_facts hs (j := 0) (by norm_num)).1
  row s hs j hj := by
    obtain ⟨hg, hm, -, hphi⟩ := row_facts hs hj
    have hpg := (phi_facts hg).1
    have hpj := (phi_facts hj).1
    have hpm := (phi_facts hm).1
    have h := cK_idx hpg hpj
    rw [← hphi] at h
    exact ((CFSG.Sporadic.Fi22.idx_eq_iff hpj hpm).1 h.symm).symm
  root := tree_facts.1
  ork_lt t ht := (tree_facts.2.1 t ht).1
  edge t ht ht0 := by
    obtain ⟨hp, hg, he⟩ := (tree_facts.2.1 t ht).2 ht0
    refine ⟨hp, hg, ?_⟩
    change ORK t = P (cJ G (E (GS (TG t))) (E (ORK (TP t))))
    rw [he, P_E (tree_facts.2.1 t ht).1]
  cover i hi := tree_facts.2.2 i hi

theorem compat {i j : ℕ} (hi : i < 3510) (hj : j < 3510) :
    Φ (P (cx i j)) = CFSG.KS.Fi22Cent.cK (Φ i) (Φ j) := by
  have h := compat_all prop_hyp (by norm_num) i hi j hj
  have hpi := (phi_facts hi).1
  have hpj := (phi_facts hj).1
  have hpm := (phi_facts (cx_star hi hj).1).1
  rw [cK_idx hpi hpj]
  exact ((CFSG.Sporadic.Fi22.idx_eq_iff hpj hpm).2 h.symm).symm

theorem cp_mem (k : ℕ) : cp k ∈ Xc := phiX_mem _

theorem wordJ_cp : ∀ w : List ℕ, (∀ k ∈ w, k < 31671) → ∀ x (hx : x < 31671),
    wordJ G w x = (((w.map cp).prod) ⟨x, hx⟩).val
  | [], _, x, hx => rfl
  | k :: w, hw, x, hx => by
    have e : wordJ G (k :: w) x = cJ G k (wordJ G w x) := rfl
    rw [e, wordJ_cp w (fun j hj => hw j (List.mem_cons_of_mem _ hj)) x hx, List.map_cons,
      List.prod_cons, Equiv.Perm.mul_apply, cJ_cp (hw k List.mem_cons_self) (Fin.isLt _)]

theorem starWord_lt : ∀ k ∈ starWord, k < 31671 := by
  intro k hk
  have := sw_facts k hk
  rw [← this.2]
  exact E_lt this.1

theorem itK_pow {p : Equiv.Perm (Fin 31671)} {f : ℕ → ℕ} (hp : ActsAs p f) :
    ∀ m x (hx : x < 31671), CFSG.KS.Fi22Cent.itK f m x = ((p ^ m) ⟨x, hx⟩).val
  | 0, x, hx => rfl
  | m + 1, x, hx => by
    have e : CFSG.KS.Fi22Cent.itK f (m + 1) x = CFSG.KS.Fi22Cent.itK f m (f x) :=
      strictN_eq (f x) _
    rw [e, ← hp x hx, itK_pow hp m _ (Fin.isLt _), pow_succ, Equiv.Perm.mul_apply]

theorem word_pow : ((starWord.map cp).prod) ^ 11 = phiX wD := by
  have hw : ActsAs ((starWord.map cp).prod) (wordJ G starWord) := fun x hx =>
    (wordJ_cp starWord starWord_lt x hx).symm
  have hmem : (phiX wD)⁻¹ * ((starWord.map cp).prod) ^ 11 ∈ Xc :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (phiX_mem _))
      (Subgroup.pow_mem _ (Xc.list_prod_mem fun p hp => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hp
        exact cp_mem k) _)
  have h1 := fix_base hmem fun q hq => by
    have hq' : q < 31671 := by omega
    have e1 : ((starWord.map cp).prod ^ 11) ⟨q, hq'⟩ = phiX wD ⟨q, hq'⟩ := Fin.ext (by
      rw [← itK_pow hw 11 q hq', pow_facts q hq, phiX_wD q hq'])
    rw [Equiv.Perm.mul_apply, e1, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
  rw [inv_mul_eq_one] at h1
  exact h1.symm

theorem rep_actTab {k : ℕ} (hk : k < 31671) :
    CFSG.Sporadic.Th.Rep 31671 (treeActTab orbLit (dTable orbLit) (genTables orbLit (-2)) k)
      (cp k) := by
  intro m hm
  unfold treeActTab
  rw [CFSG.Sporadic.Th.ap_ofFn _ hm]
  dsimp only
  rw [treeAct_cp k hk m hm, UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt ((Fin.isLt _).trans (by norm_num)), CFSG.Sporadic.Th.idx_of_lt _ hm,
    Equiv.Perm.smul_def]

theorem rep_wordTab : ∀ w : List ℕ, (∀ k ∈ w, k < 31671) →
    CFSG.Sporadic.Th.Rep 31671 (starWordTab orbLit (dTable orbLit) (genTables orbLit (-2)) w)
      (w.map cp).prod
  | [], _ => by
    simpa [starWordTab] using
      CFSG.Sporadic.Th.Rep.idT (G := Equiv.Perm (Fin 31671)) (n := 31671) (by norm_num)
  | k :: w, hw => by
    have ih := rep_wordTab w fun j hj => hw j (List.mem_cons_of_mem _ hj)
    unfold starWordTab at ih ⊢
    rw [List.foldr_cons, List.map_cons, List.prod_cons]
    exact (rep_actTab (hw k List.mem_cons_self)).compT ih

theorem powT_size (e : ℕ) (T : Table) : (powT 31671 e T).size = 31671 := by
  cases e with
  | zero => simp [powT, idT]
  | succ e => simp [powT, compT]

theorem getElem_of_ap {A B : Table} {i : ℕ} (h1 : i < A.size) (h2 : i < B.size)
    (h : ap A i = ap B i) : A[i] = B[i] := by
  unfold ap at h
  rw [getElem!_pos A i h1, getElem!_pos B i h2] at h
  exact UInt32.toNat_inj.1 h

theorem pow_table : powT 31671 11 (starWordTab orbLit (dTable orbLit) (genTables orbLit (-2)) starWord) =
    dTable orbLit := by
  have hr := (rep_wordTab starWord starWord_lt).powT (n := 31671) (by norm_num) 11
  rw [word_pow] at hr
  have hs1 := powT_size 11 (starWordTab orbLit (dTable orbLit) (genTables orbLit (-2)) starWord)
  have eD : dTable orbLit = powT 31671 7 (dWordTable orbLit) := rfl
  have hs2 := powT_size 7 (dWordTable orbLit)
  conv_rhs => rw [eD]
  refine Array.ext (hs1.trans hs2.symm) fun i h1 h2 => ?_
  have hi : i < 31671 := by rw [hs1] at h1; exact h1
  have e1 := hr i hi
  have e2 := dTable_ap hi
  rw [eD] at e2
  rw [CFSG.Sporadic.Th.idx_of_lt _ hi, Equiv.Perm.smul_def, phiX_wD i hi, ← e2] at e1
  exact getElem_of_ap h1 h2 e1

theorem dTable_star : ∀ k < 31671, ap (dTable orbLit) k = tb G 43 k := fun _ hk => dTable_ap hk

theorem pair_ok {i j : ℕ} (hi : i < 3510) (hj : j < 3510) :
    (starPhi ())[(starPos (starPts (dTable orbLit)))[treeAct orbLit.par orbLit.lab orbLit.alpha
        orbLit.beta (dTable orbLit) (genTables orbLit (-2)) (starPts (dTable orbLit))[i]!
        (starPts (dTable orbLit))[j]!]!]! =
      treeAct CFSG.Sporadic.Fi22.Native.orbL.par CFSG.Sporadic.Fi22.Native.orbL.lab
        CFSG.Sporadic.Fi22.Native.orbL.alpha CFSG.Sporadic.Fi22.Native.orbL.beta
        CFSG.Sporadic.Fi22.Native.orbL.alpha
        (CFSG.Sporadic.Fi22.Native.genTables CFSG.Sporadic.Fi22.Native.orbL (-2))
        (starPhi ())[i]! (starPhi ())[j]! := by
  have hs := cx_star hi hj
  rw [starPts_get dTable_star hi, starPts_get dTable_star hj, treeAct_cp _ (E_lt hi) _ (E_lt hj),
    ← cx_cp hi hj, starPos_get dTable_star (by rw [← hs.2]; exact mem_EL hs.1),
    starPhi_get hs.1, starPhi_get hi, starPhi_get hj, compat hi hj,
    treeAct_cTab _ _ (phi_facts hj).1,
    CertificateChecks.KernelFi22Cent.cTab_eq (phi_facts hi).1 (phi_facts hj).1]

theorem cent_ok :
    centChecks (orbitData ()) (CFSG.Sporadic.Fi22.Native.orbitData ()) 3 = true := by
  rw [orbitData_eq', CertificateChecks.KernelFi22C.orbitData_eq]
  unfold centChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    exact starPts_size dTable_star
  · rw [beq_iff_eq]
    exact starPhi_size
  · refine CFSG.Sporadic.Th.allIn_eq_true.2 fun i _ hi => ?_
    have hp := phi_facts hi
    rw [starPhi_get hi, starPhiPos_get hp.1, hp.2.2.1]
    simp [hp.1]
  · refine CFSG.Sporadic.Th.parAll_eq_true_of fun i hi =>
      CFSG.Sporadic.Th.allIn_eq_true.2 fun j _ hj => ?_
    rw [beq_iff_eq]
    exact pair_ok hi hj
  · refine List.all_eq_true.2 fun k hk => ?_
    have h := sw_facts k hk
    rw [Array.contains_iff_mem, ← Array.mem_toList_iff, starPts_toList dTable_star, ← h.2]
    exact mem_EL h.1
  · rw [beq_iff_eq]
    exact pow_table

end

end CertificateChecks.KernelFi23C

end
