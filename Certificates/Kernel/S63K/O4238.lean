module

public import Certificates.Kernel.S63K.OChecks
public import Certificates.Kernel.S63K.OMerge
public import Certificates.Kernel.S63K.L4234
public import CFSG.Certificates.Kernel.MergeTGSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS63.O4238

open CFSG.D4Hex CFSG.KC.S63K CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Certificates CertificateChecks.KernelS63
  CertificateChecks.KernelS63.HD

theorem beqT {a b : ℕ} (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

theorem ext! {a b : Array ℕ} (n : ℕ) (ha : a.size = n) (hb : b.size = n)
    (h : ∀ i < n, a[i]! = b[i]!) : a = b := by
  apply Array.ext (by rw [ha, hb])
  intro i h1 h2
  have := h i (by omega)
  rwa [getElem!_pos a i h1, getElem!_pos b i h2] at this

theorem unpack_size (n w P : ℕ) : (unpack n w P).size = n := by
  unfold unpack
  exact Array.size_ofFn

theorem canon_lt {n w P : ℕ} (h : canonK n w (mask w) (n * w) P = true) :
    ∀ i < n, pg w (mask w) P i < n := by
  intro i hi
  unfold canonK at h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨-, h⟩ := (bAnd_iff _ _).1 h
  exact Nat.blt_eq.mp (allN_spec h i hi)

theorem cAll : allN 8 (fun i => canonK 7371 13 (mask 13) (7371 * 13) (OD.D i)) = true ∧
    allN 5 (fun i => canonK 7371 13 (mask 13) (7371 * 13) (OK.GB i)) = true ∧
    allN 4 (fun i => canonK 819 12 (mask 12) (819 * 12) (OK.GU i)) = true := by
  have h := OK.ch4238C
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem cD : allN 8 (fun i => canonK 7371 13 (mask 13) (7371 * 13) (OD.D i)) = true := cAll.1

theorem cB : allN 5 (fun i => canonK 7371 13 (mask 13) (7371 * 13) (OK.GB i)) = true := cAll.2.1

theorem cU : allN 4 (fun i => canonK 819 12 (mask 12) (819 * 12) (OK.GU i)) = true := cAll.2.2

theorem fl_lt {j c : ℕ} (hj : j < 8) (hc : c < 7371) : OK.fl j c < 7371 := by
  unfold OK.fl
  rw [pgW_eq]
  exact canon_lt (allN_spec cD j hj) c hc

theorem lf_lt {i : ℕ} (hi : i < 7371) : GD.LTf i < 819 := (lt_get hi).2

theorem flag_get {j c : ℕ} (hj : j < 8) (hc : c < 7371) : flagGen j c = OK.fl j c := by
  have h := allN_spec (allN_spec OK.ch4238F j hj) c hc
  rw [CFSG.KC.MergeG.strictB_eqM] at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  have hl : c / 3 < 2457 := by omega
  have hf : OK.fl j c / 3 < 2457 := Nat.blt_eq.mp h1
  have hk : imgKey j (c / 3) = keyF GD.LTf (OK.fl j c / 3) := by
    unfold imgKey
    rw [L4234.lnPt0, L4234.lnPt1, L4234.lnPt2,
      perm_get (x := GD.LTf (3 * (c / 3))) hj (lf_lt (by omega)),
      perm_get (x := GD.LTf (3 * (c / 3) + 1)) hj (lf_lt (by omega)),
      perm_get (x := GD.LTf (3 * (c / 3) + 2)) hj (lf_lt (by omega)), L4234.sortKey_eq]
    exact (beqT h2).symm
  have hp : (permArrs[j]!)[lnPt (c / 3) (c % 3)]! = im j (OK.lf c) := by
    unfold lnPt
    rw [G4235.hP, Nat.div_add_mod]
    exact perm_get hj (lf_lt hc)
  unfold flagGen
  dsimp only
  rw [hp, hk, L4234.idx_key hf, L4234.lnPt0, L4234.lnPt1]
  conv_rhs => rw [beqT h3]
  unfold OK.posF
  rw [CFSG.KC.MergeG.nIf_beq, CFSG.KC.MergeG.nIf_beq]
  rfl

theorem flagArrs_get {j : ℕ} (hj : j < 8) : flagArrs[j]! = unpack 7371 13 (OD.D j) := by
  have e1 : flagArrs[j]! = flagArr j := by
    rw [getElem!_pos flagArrs j (by simp [flagArrs, hj])]
    simp [flagArrs]
  rw [e1]
  refine ext! 7371 (by simp [flagArr]) (unpack_size _ _ _) fun c hc => ?_
  unfold flagArr
  rw [getElem!_pos _ c (by simp [hc]), Array.getElem_ofFn]
  change flagGen j c = _
  rw [flag_get hj hc, unpackW_get hc]
  exact pgW_eq _ _ _

theorem hgD : flagArrs.size = 8 ∧ ∀ i < 8, flagArrs[i]! = unpack 7371 13 (OD.D i) :=
  ⟨by simp [flagArrs], fun _ hi => flagArrs_get hi⟩

theorem fa_get {j c : ℕ} (hj : j < 8) (hc : c < 7371) : (flagArrs[j]!)[c]! = OK.fl j c := by
  rw [flagArrs_get hj, unpackW_get hc]
  exact (pgW_eq _ _ _).symm

theorem idA_get {n i : ℕ} (hi : i < n) : (idA n)[i]! = i := by
  unfold idA
  rw [getElem!_pos _ i (by simp [hi]), Array.getElem_ofFn]

theorem compA_size (n : ℕ) (t u : Array ℕ) : (compA n t u).size = n := by
  unfold compA
  exact Array.size_ofFn

theorem zf_eq : flagWordArr [3, 2, 4, 2] = unpack 7371 13 (OD.D 8) := by
  refine ext! 7371 (compA_size _ _ _) (unpack_size _ _ _) fun c hc => ?_
  have h := beqT (allN_spec OK.ch4238Z c hc)
  unfold flagWordArr
  simp only [List.foldr]
  have l2 : OK.fl 2 c < 7371 := fl_lt (by norm_num) hc
  have l4 : OK.fl 4 (OK.fl 2 c) < 7371 := fl_lt (by norm_num) l2
  have l2' : OK.fl 2 (OK.fl 4 (OK.fl 2 c)) < 7371 := fl_lt (by norm_num) l4
  rw [compA_get' hc, compA_get' hc, compA_get' hc, compA_get' hc, idA_get hc,
    fa_get (j := 2) (by norm_num) hc, fa_get (j := 4) (by norm_num) l2,
    fa_get (j := 2) (by norm_num) l4, fa_get (j := 3) (by norm_num) l2',
    unpackW_get hc, ← pgW_eq, h]

theorem hgB : bFlagArrs.size = 5 ∧ ∀ i < 5, bFlagArrs[i]! = unpack 7371 13 (OK.GB i) := by
  refine ⟨rfl, fun i hi => ?_⟩
  unfold bFlagArrs
  rw [getElem!_pos _ i (by simpa using hi)]
  interval_cases i <;>
    simp only [List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero]
  · exact flagArrs_get (j := 0) (by norm_num)
  · exact flagArrs_get (j := 1) (by norm_num)
  · exact flagArrs_get (j := 2) (by norm_num)
  · exact flagArrs_get (j := 6) (by norm_num)
  · exact zf_eq

theorem permArrs_get {k : ℕ} (hk : k < 8) : permArrs[k]! = unpack 819 12 (PA k) := by
  have e1 : permArrs[k]! = permArr k := by
    rw [getElem!_pos permArrs k (by rw [permArrs_size]; exact hk)]
    simp [permArrs]
  refine ext! 819 (by rw [e1]; exact permArr_size k) (unpack_size _ _ _) fun x hx => ?_
  rw [perm_get hk hx, unpackW_get hx]
  rfl

theorem hgU : uPtArrs.size = 4 ∧ ∀ i < 4, uPtArrs[i]! = unpack 819 12 (OK.GU i) := by
  refine ⟨rfl, fun i hi => ?_⟩
  interval_cases i
  · exact permArrs_get (k := 0) (by norm_num)
  · exact permArrs_get (k := 1) (by norm_num)
  · exact permArrs_get (k := 2) (by norm_num)
  · exact permArrs_get (k := 6) (by norm_num)

theorem rAll : Nat.beq (pg 13 (mask 13) (OD.D 31) 0) 0 = true ∧
    (∀ c < 12, Nat.beq (pg 13 (mask 13) (OD.D 32) c) (ovReps.getD c 0) = true) ∧
    ∀ c < 6, Nat.beq (pg 12 (mask 12) (OD.D 33) c) (ovURep.getD c 0) = true := by
  have h := OK.ch4238R
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true,
    CFSG.KS.SporSch.M24.MatL.allN_iff] at h
  exact h

theorem repD : (#[0] : Array ℕ).size = 1 ∧ ∀ c < 1, (#[0] : Array ℕ)[c]! = pg 13 (mask 13) (OD.D 31) c := by
  refine ⟨rfl, fun c hc => ?_⟩
  have e : c = 0 := by omega
  subst e
  exact (beqT rAll.1).symm

theorem repB : ovReps.toArray.size = 12 ∧ ∀ c < 12, ovReps.toArray[c]! = pg 13 (mask 13) (OD.D 32) c := by
  refine ⟨rfl, fun c hc => ?_⟩
  rw [G4235.toArray_get]
  exact (beqT (rAll.2.1 c hc)).symm

theorem repU : ovURep.toArray.size = 6 ∧ ∀ c < 6, ovURep.toArray[c]! = pg 12 (mask 12) (OD.D 33) c := by
  refine ⟨rfl, fun c hc => ?_⟩
  rw [G4235.toArray_get]
  exact (beqT (rAll.2.2 c hc)).symm

theorem dAll : bfsTK 7371 13 OD.D 8 1 (OD.D 31) 7371 (OD.D 9) (OD.D 10) (OD.D 11) (OD.D 12) (OD.D 13)
      (OD.D 14) (OD.D 15) = true ∧
    labOKK 7371 13 OD.D 8 1 (OD.D 12) (OD.D 31) (OD.D 13) (OD.D 14) (OD.D 15) = true := by
  have h := OK.ch4238D
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem bAll : bfsTK 7371 13 OK.GB 5 12 (OD.D 32) 7371 (OD.D 16) (OD.D 17) (OD.D 18) (OD.D 19)
      (OD.D 20) (OD.D 21) (OD.D 22) = true ∧
    labOKK 7371 13 OK.GB 5 12 (OD.D 19) (OD.D 32) (OD.D 20) (OD.D 21) (OD.D 22) = true := by
  have h := OK.ch4238B
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem uAll : bfsTK 819 12 OK.GU 4 6 (OD.D 33) 819 (OD.D 23) (OD.D 24) (OD.D 25) (OD.D 26)
      (OD.D 27) (OD.D 28) (OD.D 29) = true ∧
    labOKK 819 12 OK.GU 4 6 (OD.D 26) (OD.D 33) (OD.D 27) (OD.D 28) (OD.D 29) = true := by
  have h := OK.ch4238U
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem forD : ovDForest = (unpack 7371 13 (OD.D 12), unpack 7371 13 (OD.D 13),
    unpack 7371 13 (OD.D 14), unpack 7371 13 (OD.D 15)) :=
  bfsTK_sound (by norm_num) hgD cD repD dAll.1

theorem forB : ovBForest = (unpack 7371 13 (OD.D 19), unpack 7371 13 (OD.D 20),
    unpack 7371 13 (OD.D 21), unpack 7371 13 (OD.D 22)) :=
  bfsTK_sound (by norm_num) hgB cB repB bAll.1

theorem forU : ovUForest = (unpack 819 12 (OD.D 26), unpack 819 12 (OD.D 27),
    unpack 819 12 (OD.D 28), unpack 819 12 (OD.D 29)) :=
  bfsTK_sound (by norm_num) hgU cU repU uAll.1

theorem labD : orbitLabelOK 7371 flagArrs 1 (unpack 7371 13 (OD.D 12)) #[0]
    (unpack 7371 13 (OD.D 13)) (unpack 7371 13 (OD.D 14)) (unpack 7371 13 (OD.D 15)) = true :=
  labOKK_sound (by norm_num) hgD cD repD dAll.2

theorem labB : orbitLabelOK 7371 bFlagArrs 12 (unpack 7371 13 (OD.D 19)) ovReps.toArray
    (unpack 7371 13 (OD.D 20)) (unpack 7371 13 (OD.D 21)) (unpack 7371 13 (OD.D 22)) = true :=
  labOKK_sound (by norm_num) hgB cB repB bAll.2

theorem labU : orbitLabelOK 819 uPtArrs 6 (unpack 819 12 (OD.D 26)) ovURep.toArray
    (unpack 819 12 (OD.D 27)) (unpack 819 12 (OD.D 28)) (unpack 819 12 (OD.D 29)) = true :=
  labOKK_sound (by norm_num) hgU cU repU uAll.2

theorem mergeBytes : ovMergeText.toUTF8 = (String.ofList OD.MC).toUTF8 := by rw [OD.MC_eq]

theorem tAll : lowK OD.MC 0 (OD.D 30) = true ∧ OD.MC.length = 40149 := by
  have h := OM.ch4238T
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem lowM : lowK OD.MC 0 (OD.D 30) = true := tAll.1

theorem lenM : OD.MC.length = 40149 := tAll.2

theorem off_eq {j : ℕ} (hj : j < 9) : (ovMergeLens.take j).foldl (· + ·) 0 = OM.off j ∧
    OM.off j + ovMergeLens.getD j 0 ≤ 4461 := by
  interval_cases j <;> exact ⟨rfl, by decide⟩

theorem mv_eq {j : ℕ} (hj : j < 9) : mergeVals (ovMerge j) =
    (List.range (ovMergeLens.getD j 0)).map fun k => (OM.RI j k, OM.RU j k, OM.RV j k) := by
  obtain ⟨e1, e2⟩ := off_eq hj
  unfold ovMerge mergeVals
  dsimp only
  rw [List.map_map, e1, mergeBytes]
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.1 hr
  have hb : ∀ k, k < 9 * (OM.off j + r) + 9 → CFSG.D4Hex.hexVal
      ((String.ofList OD.MC).toUTF8.get! k) = OM.mD k := fun k hk =>
    byte_low lowM (by rw [lenM]; omega)
  simp (disch := omega) only [Function.comp_apply, hexAtW, hb]
  rfl

theorem mOK_get {j : ℕ} (hj : j < 9) : OM.mOK j = true := by
  interval_cases j
  exacts [OM.m0, OM.m1, OM.m2, OM.m3, OM.m4', OM.m5, OM.m6, OM.m7, OM.m8]

theorem merge_get {j : ℕ} (hj : j < 9) :
    CFSG.Quasithin.mergeTargetsOK 7371 flagArrs 0 ovReps[j + 3]! (mergeVals (ovMerge j)) [1, 3] =
      true := by
  have hx : ovReps[j + 3]! = ovReps.getD (j + 3) 0 := by
    interval_cases j <;> rfl
  rw [hx]
  exact CFSG.KC.MergeG.mergeTargetsOK_of_mergeTCKG (by norm_num) hgD cD (mv_eq hj) (mOK_get hj)

theorem pw_size : ∀ w : List ℕ, (ptWordArr w).size = 819
  | [] => by simp [ptWordArr, idA]
  | _ :: _ => compA_size _ _ _

theorem pw_get : ∀ w : List ℕ, (∀ k ∈ w, k < 8) → ∀ x < 819,
    (ptWordArr w)[x]! = ptW w x ∧ ptW w x < 819
  | [], _, x, hx => ⟨idA_get hx, hx⟩
  | k :: w, hw, x, hx => by
    obtain ⟨h1, h2⟩ := pw_get w (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')) x hx
    have hk := hw k List.mem_cons_self
    have e : ptWordArr (k :: w) = compA 819 permArrs[k]! (ptWordArr w) := rfl
    have e2 : ptW (k :: w) x = im k (ptW w x) := rfl
    rw [e, compA_get' hx, h1, perm_get hk h2, e2]
    exact ⟨rfl, (pa_get hk h2).2⟩

theorem im_lt {k x : ℕ} (hk : k < 8) (hx : x < 819) : im k x < 819 := (pa_get hk hx).2

theorem zt_get {x : ℕ} (hx : x < 819) : (ptWordArr [3, 2, 4, 2])[x]! = OK.zt x ∧ OK.zt x < 819 :=
  pw_get _ (by decide) x hx

theorem pow_get (k : ℕ) : (ptPowArr (ptWordArr [3, 2, 4, 2]) k).size = 819 ∧
    ∀ x < 819, (ptPowArr (ptWordArr [3, 2, 4, 2]) k)[x]! = OK.zIt k x ∧ OK.zIt k x < 819 := by
  induction k with
  | zero => exact ⟨by simp [ptPowArr, idA], fun x hx => ⟨idA_get hx, hx⟩⟩
  | succ k ih =>
    refine ⟨compA_size _ _ _, fun x hx => ?_⟩
    obtain ⟨h1, h2⟩ := ih.2 x hx
    have e : ptPowArr (ptWordArr [3, 2, 4, 2]) (k + 1) =
        compA 819 (ptWordArr [3, 2, 4, 2]) (ptPowArr (ptWordArr [3, 2, 4, 2]) k) := rfl
    rw [e, compA_get' hx, h1]
    exact zt_get h2

theorem comp_get {x : ℕ} (hx : x < 819) {u v : List ℕ} (hu : ∀ k ∈ u, k < 8)
    (hv : ∀ k ∈ v, k < 8) : (compA 819 (ptWordArr u) (ptWordArr v))[x]! = ptW u (ptW v x) := by
  rw [compA_get' hx, (pw_get v hv x hx).1, (pw_get u hu _ (pw_get v hv x hx).2).1]

theorem perm_w {k : ℕ} (hk : k < 8) : permArrs[k]! = ptWordArr [k] :=
  ext! 819 (by rw [permArrs_get hk]; exact unpack_size _ _ _) (pw_size _) fun x hx => by
    rw [perm_get hk hx, (pw_get [k] (by simpa using hk) x hx).1]
    rfl

theorem fix_eq (a : Array ℕ) : fixesLine0 a = (sortKeyF a[0]! a[1]! a[5]! == 824) := by
  unfold fixesLine0
  rw [L4234.sortKey_eq]
  rfl

theorem zeta_parts : ovZetaCheck = true := by
  have h := OK.ch4238Zt
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true, Bool.not_eq_true',
    CFSG.KS.SporSch.M24.MatL.allN_iff, Nat.beq_eq, beq_iff_eq, beq_eq_false_iff_ne,
    ne_eq] at h
  obtain ⟨h0, hl, hall, hne, h7, h7l, h3, h3l⟩ := h
  have w1 : ∀ k ∈ [3, 2, 4, 2], k < 8 := by decide
  have pz : ∀ x < 819, (ptWordArr [3, 2, 4, 2])[x]! = OK.zt x := fun x hx => (zt_get hx).1
  have cq : ∀ (a b c d : List ℕ), (∀ k ∈ a, k < 8) → (∀ k ∈ b, k < 8) → (∀ k ∈ c, k < 8) →
      (∀ k ∈ d, k < 8) → (∀ x < 819, ptW a (ptW b x) = ptW c (ptW d x)) →
      compA 819 (ptWordArr a) (ptWordArr b) = compA 819 (ptWordArr c) (ptWordArr d) :=
    fun a b c d ha hb hc hd hx => ext! 819 (compA_size _ _ _) (compA_size _ _ _) fun x hx' => by
      rw [comp_get hx' ha hb, comp_get hx' hc hd, hx x hx']
  unfold ovZetaCheck
  rw [perm_w (k := 0) (by norm_num), perm_w (k := 1) (by norm_num), perm_w (k := 2) (by norm_num),
    perm_w (k := 6) (by norm_num)]
  simp only [fix_eq, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
    beq_eq_false_iff_ne]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [pz 0 (by norm_num), h0]
  · rw [pz 0 (by norm_num), pz 1 (by norm_num), pz 5 (by norm_num), hl]
  · refine ext! 819 (pow_get 7).1 (by simp [idA]) fun x hx => ?_
    rw [(pow_get 7).2 x hx |>.1, idA_get hx]
    exact (hall x hx).1.1.1.1
  · exact cq _ _ _ _ w1 (by decide) (by decide) w1 fun x hx => (hall x hx).1.1.1.2
  · exact cq _ _ _ _ w1 (by decide) (by decide) w1 fun x hx => (hall x hx).1.1.2
  · exact cq _ _ _ _ w1 (by decide) (by decide) w1 fun x hx => (hall x hx).1.2
  · exact cq _ _ _ _ w1 (by decide) (by decide) w1 fun x hx => (hall x hx).2
  · intro he
    have ht : allN 819 (fun x => OK.zt (im 0 x) == im 0 (OK.zt x)) = true :=
      CFSG.KS.SporSch.M24.MatL.allN_iff.2 fun x hx => by
        have := congrArg (fun a : Array ℕ => a[x]!) he
        rw [comp_get hx w1 (by decide), comp_get hx (by decide) w1] at this
        exact beq_iff_eq.2 this
    rw [ht] at hne
    exact Bool.noConfusion hne
  · rw [perm_get (k := 7) (x := 0) (by norm_num) (by norm_num)]
    exact h7
  · rw [perm_get (k := 7) (x := 0) (by norm_num) (by norm_num),
      perm_get (k := 7) (x := 1) (by norm_num) (by norm_num),
      perm_get (k := 7) (x := 5) (by norm_num) (by norm_num)]
    exact h7l
  · rw [perm_get (k := 3) (x := 0) (by norm_num) (by norm_num)]
    exact h3
  · rw [perm_get (k := 3) (x := 0) (by norm_num) (by norm_num),
      perm_get (k := 3) (x := 1) (by norm_num) (by norm_num),
      perm_get (k := 3) (x := 5) (by norm_num) (by norm_num)]
    exact h3l

theorem flag_parts : ovFlagCheck = true := by
  have hL := OK.ch4238L
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hL
  obtain ⟨hl2, hfl, -, hl3, -⟩ := hL
  unfold ovFlagCheck
  rw [forD, forB]
  dsimp only
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgD.1, hgB.1⟩, labD⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, labB⟩, ?_⟩, ?_⟩, rfl⟩,
    ?_⟩, ?_⟩
  · rw [unpackW_get (by norm_num), ← pgW_eq]
    exact hl2
  · refine CFSG.KC.MergeG.allLt_of fun c hc => ?_
    have h := CFSG.KS.SporSch.M24.MatL.allN_iff.1 hfl c hc
    unfold lnPt
    rw [G4235.hP, Nat.div_add_mod, unpackW_get hc, ← pgW_eq]
    exact h
  · exact CFSG.KC.MergeG.allLt_of fun j hj => merge_get hj
  · rw [L4234.lnPt0]
    exact hl3

theorem u_parts : ovUCheck = true := by
  have hL := OK.ch4238L
  simp only [CFSG.KS.SporSch.M24.MatL.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hL
  obtain ⟨-, -, hu5, -, hcnt⟩ := hL
  unfold ovUCheck
  rw [forU]
  dsimp only
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨hgU.1, rfl⟩, rfl⟩, rfl⟩, labU⟩, ?_⟩, ?_⟩
  · rw [unpackW_get (by norm_num), ← pgW_eq]
    exact hu5
  · have hc := CFSG.KS.SporSch.M24.MatL.allN_iff.1 hcnt
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, cntK_sound, beqT (hc i h1), List.getD_eq_getElem]

open Certificates in
theorem c4238 : CFSG.D4Hex.overCheck = true := by
  unfold overCheck
  rw [flag_parts, u_parts, zeta_parts]
  rfl

end CertificateChecks.KernelS63.O4238

end
