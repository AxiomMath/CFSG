
module

public import Certificates.Kernel.SporSch.HN.ArrStrong
public import Certificates.Kernel.SporSch.HN.Invol2099
public import Certificates.Kernel.SporSch.HN.Local2100K
public import CFSG.Certificates.Kernel.SporSch.HNNat
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNLocal

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native CFSG.Sporadic.He.Native
open CFSG.Sporadic.He CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNInvol
open CertificateChecks.KernelSporSch.HNArrS CFSG.KS.TW Matrix

theorem mat_hJ1 :
    matJ hJ1 = toMat 5 133 (colsMat 133 (rows5 (sx 21))) := by
  rw [runProg_mat prog_lt (k := 1) (by omega), HNStrong.regs_12.1]
  have : HNStrong.SA[0]! = HNStrong.F 0 := ofFn_getElem! (F := HNStrong.F) (by omega)
  rw [← this, H0_eq]
  rfl

theorem mat_hJ2 :
    matJ hJ2 = toMat 5 133 (colsMat 133 (rows5 (sx 22))) := by
  rw [runProg_mat prog_lt (k := 2) (by omega), HNStrong.regs_12.2]
  have : HNStrong.SA[1]! = HNStrong.F 1 := ofFn_getElem! (F := HNStrong.F) (by omega)
  rw [← this, H1_eq]
  rfl

noncomputable abbrev XV (i : ℕ) : Fin 133 → ZMod 5 := toVec 5 133 (vec5 (sx 58 i))

theorem mat_x {h : JH} {k : ℕ} (hk : k < 62)
    (hm : matJ h = toMat 5 133 (colsMat 133 (rows5 (sx k)))) {i : ℕ} (hi : i < 462) :
    matJ h *ᵥ XV i = toVec 5 133 (vec5 (vm5 (sx k) (sx 58 i))) := by
  rw [hm, XV, ← toVec_mulVec, mulVec5_sound (canon k hk) (canonX i hi)]

theorem getElem!_getD (l : List (ℕ × ℕ)) (i : ℕ) : l[i]! = l.getD i (0, 0) := by
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [getElem!_pos l i h, List.getD_eq_getElem _ _ h]
  · rw [getElem!_neg l i (by omega), List.getD_eq_default _ _ h]
    rfl

theorem parents_rec (i : ℕ) (h1 : 1 ≤ i) (hi : i < 462) :
    LocalData.parents[i]!.1 < i ∧ (LocalData.parents[i]!.2 = 1 ∨ LocalData.parents[i]!.2 = 2) ∧
      vm5 (sx (if LocalData.parents[i]!.2 = 1 then 21 else 22)) (sx 58 LocalData.parents[i]!.1) =
        sx 58 i := by
  obtain ⟨a, b, c⟩ := xrec i h1 hi
  rw [getElem!_getD]
  refine ⟨a, b, ?_⟩
  rcases b with e | e
  · rw [e] at c ⊢
    exact c
  · rw [e] at c ⊢
    exact c

noncomputable abbrev xs : Array ℕ :=
  xIndex SJ (seedWordIdx (arrJ aJ) (arrJ bJ) LocalData.rootWord 0) LocalData.parents

theorem xs_spec : xs.size = LocalData.parents.length ∧
    xs[0]! = seedWordIdx (arrJ aJ) (arrJ bJ) LocalData.rootWord 0 ∧
    ∀ i, 1 ≤ i → i < LocalData.parents.length →
      xs[i]! = (SJ[LocalData.parents[i]!.2 - 1]!)[xs[LocalData.parents[i]!.1]!]! :=
  xIndex_spec SJ (seedWordIdx (arrJ aJ) (arrJ bJ) LocalData.rootWord 0)
  (recs := LocalData.parents) (by rw [parents_len]; omega)
  (fun i h1 hi => (parents_rec i h1 (by rw [parents_len] at hi; exact hi)).1)

theorem PK_xs : ∀ i < 462, xs[i]! < nPts ∧ PK xs[i]! = XV i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    obtain ⟨-, h0, hs⟩ := xs_spec
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [h0]
      have hv : PK 0 = toVec 5 133 rootVec := by rw [PK_zero, toVec_rootVec]
      obtain ⟨hlt, he⟩ := PK_seedWordIdx LocalData.rootWord root_mem (x := 0) (by decide) _ hv
      refine ⟨hlt, ?_⟩
      rw [he, XV, rowsA_eq, rowsB_eq, rootVec_eq, x0_eq, ← x0_row]
      rfl
    · obtain ⟨hp, he, hv⟩ := parents_rec i hpos hi
      obtain ⟨ihl, ihe⟩ := ih _ hp (by omega)
      rw [hs i hpos (by rw [parents_len]; exact hi)]
      rcases he with e | e
      · rw [e, show 1 - 1 = 0 from rfl, SJ_get (j := 0) (by omega), arrJ_get _ ihl, sL0]
        refine ⟨gi_lt _ ihl, ?_⟩
        rw [e, ite_eq_left rfl] at hv
        rw [PK_gi _ ihl, ihe, mat_x (k := 21) (by omega) mat_hJ1
          (i := LocalData.parents[i]!.1) (by omega), hv]
      · rw [e, show 2 - 1 = 1 from rfl, SJ_get (j := 1) (by omega), arrJ_get _ ihl, sL1]
        refine ⟨gi_lt _ ihl, ?_⟩
        rw [e, ite_eq_right (by omega)] at hv
        rw [PK_gi _ ihl, ihe, mat_x (k := 22) (by omega) mat_hJ2
          (i := LocalData.parents[i]!.1) (by omega), hv]

theorem lane5_eq (x j : ℕ) : lane5 x j = (x >>> (16 * j)) &&& 65535 := rfl

theorem eq_of_lanes {x y : ℕ} (hx : canon5 x = true) (hy : canon5 y = true)
    (h : ∀ j < 133, lane5 x j = lane5 y j) : x = y := by
  have hx0 : x >>> 2128 = 0 := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 hx).1
  have hy0 : y >>> 2128 = 0 := Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 hy).1
  apply Nat.eq_of_testBit_eq
  intro k
  rcases Nat.lt_or_ge k 2128 with hk | hk
  · have e := congrArg (fun z => z.testBit (k % 16)) (h (k / 16) (by omega))
    simp only [lane5_eq, Nat.testBit_and, Nat.testBit_shiftRight] at e
    have h65 : (65535 : ℕ).testBit (k % 16) = true := by
      have : (65535 : ℕ) = 2 ^ 16 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]
      simp [Nat.mod_lt k (by omega : 16 > 0)]
    rw [h65, Bool.and_true, Bool.and_true, show 16 * (k / 16) + k % 16 = k by omega] at e
    exact e
  · have ex := congrArg (fun z => z.testBit (k - 2128)) hx0
    have ey := congrArg (fun z => z.testBit (k - 2128)) hy0
    simp only [Nat.testBit_shiftRight, Nat.zero_testBit, show 2128 + (k - 2128) = k by omega] at ex ey
    rw [ex, ey]

theorem XV_inj {i j : ℕ} (hi : i < 462) (hj : j < 462) (h : XV i = XV j) : sx 58 i = sx 58 j := by
  have hc : ∀ m < 462, canonV 5 133 (vec5 (sx 58 m)) = true := fun m hm => by
    simp only [canonV, Bool.and_eq_true, beq_iff_eq]
    exact ⟨by simp [vec5], vec5_all (canonX m hm)⟩
  have e := eq_of_toVec_eq (hc i hi) (hc j hj) h
  refine eq_of_lanes (canonX i hi) (canonX j hj) fun t ht => ?_
  have := congrArg (fun v : Array ℕ => v[t]!) e
  simpa [vec5, getElem!_ofFn _ ht] using this

theorem dist (i : ℕ) (hi : i < 462) : ∀ j < i, sx 58 j ≠ sx 58 i := by
  have h : distB i = true := by
    rcases Nat.lt_or_ge i 231 with a | a
    · have := allBlk_spec dist0 i a
      rwa [show Nat.add 0 i = i by rw [Nat.add_eq]; omega] at this
    · have := allBlk_spec dist1 (i - 231) (by omega)
      rwa [show Nat.add 231 (i - 231) = i by rw [Nat.add_eq]; omega] at this
  intro j hj e
  have := allN_spec h j hj
  rw [e, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem img (k : ℕ) (l : Array ℕ) (ha : allBlk 0 (imgB k l) 231 = true)
    (hb : allBlk 231 (imgB k l) 231 = true) {i : ℕ} (hi : i < 462) :
    vm5 (sx k) (sx 58 i) = sx 58 l[i]! := by
  have h : imgB k l i = true := by
    rcases Nat.lt_or_ge i 231 with a | a
    · have := allBlk_spec ha i a
      rwa [show Nat.add 0 i = i by rw [Nat.add_eq]; omega] at this
    · have := allBlk_spec hb (i - 231) (by omega)
      rwa [show Nat.add 231 (i - 231) = i by rw [Nat.add_eq]; omega] at this
  exact Nat.eq_of_beq_eq_true h

theorem lperm_lt : (∀ i < 462, LocalData.lperm1[i]! < 462 ∧ LocalData.lperm2[i]! < 462) ∧
    LocalData.lperm1.size = 462 ∧ LocalData.lperm2.size = 462 := by
  decide +kernel

theorem img_idx {h : JH} {k : ℕ} (hk : k < 62)
    (hm : matJ h = toMat 5 133 (colsMat 133 (rows5 (sx k)))) {l : Array ℕ}
    (hl : ∀ i < 462, vm5 (sx k) (sx 58 i) = sx 58 l[i]!) (hlt : ∀ i < 462, l[i]! < 462)
    {i : ℕ} (hi : i < 462) : gi h xs[i]! = xs[l[i]!]! := by
  obtain ⟨h1, h2⟩ := PK_xs i hi
  obtain ⟨h3, h4⟩ := PK_xs _ (hlt i hi)
  refine PK_injective _ (gi_lt _ h1) _ h3 ?_
  rw [PK_gi _ h1, h2, mat_x hk hm hi, hl i hi, h4]

theorem nat1 : strongOK 12 (natArr LocalData.natGen1) (natArr LocalData.natGen2)
    (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2] LocalData.strongWords)
    LocalData.strongWords = true := HNNat.natStrongOK

theorem nat2 : allBelowN 17 (fun j => peq 12
    (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
      LocalData.strongWords)[j]! (natArr LocalData.strongImages[j]!)) = true :=
  CFSG.ONSchreier.allBelowN_iff.2 fun _ hj => HNNat.peq_maps fun _ hx => HNNat.natS_pt hj hx

@[expose] def cyc (k x : ℕ) : ℕ := if x = 0 then 1 else if x = 1 then k else if x = k then 0 else x

theorem cycle01_get {k x : ℕ} (hx : x < 12) : (cycle01 k)[x]! = cyc k x := by
  rw [cycle01, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]
  rfl

theorem triple_facts : ∀ i < 10, plettersOK 17 LocalData.tripleWords[i]! = true ∧
    ∀ x < 12, LocalData.tripleWords[i]!.foldr (GZ HNNat.natF HNNat.natFI) x = cyc (i + 2) x := by
  decide +kernel

theorem nat3 : allBelowN 10 (fun i => plettersOK 17 LocalData.tripleWords[i]! &&
    peq 12 (pword 12 (extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
      LocalData.strongWords) (pinvs 12 (extendStrong 12 #[natArr LocalData.natGen1,
        natArr LocalData.natGen2] LocalData.strongWords)) LocalData.tripleWords[i]!)
      (cycle01 (i + 2))) = true := by
  refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
  obtain ⟨hp, hf⟩ := triple_facts i hi
  rw [hp, HNNat.peq_maps fun x hx => by
    rw [HNNat.natWord_pt (plettersOK_iff.1 hp) hx, cycle01_get hx, hf x hx]]
  rfl

theorem sizes : LocalData.strongImages.size = 17 ∧ LocalData.tripleWords.size = 10 ∧
    LocalData.parents.length = 462 := by decide +kernel

theorem parents_ok : ∀ i < 462, i ≠ 0 → (decide (LocalData.parents[i]!.1 < i) &&
    (LocalData.parents[i]!.2 == 1 || LocalData.parents[i]!.2 == 2)) = true := by
  intro i hi h0
  obtain ⟨a, b, -⟩ := parents_rec i (by omega) hi
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  exact ⟨a, b⟩

theorem localChecks_arr :
    localChecks nPts (arrJ aJ) (arrJ bJ) = true := by
  obtain ⟨xsz, x0e, xse⟩ := xs_spec
  rw [parents_len] at xsz
  obtain ⟨hlt, hl1, hl2⟩ := lperm_lt
  unfold localChecks
  try dsimp only
  rw [regs_get (k := 1) (by omega), regs_get (k := 2) (by omega), hS_eq]
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq]
  refine ⟨strongOK_arrJ HNStrong.strong_parts.1 (by omega) words_lt, nat1, sizes.1, nat2,
    sizes.2.1, nat3, sizes.2.2, xsz, x0e, ?_, ?_, ?_, hl1, hl2, ?_⟩
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rfl
    · have hp := parents_ok i hi (by omega)
      have h0 : (i == 0) = false := beq_eq_false_iff_ne.2 (by omega)
      rw [xse i hpos (by rw [parents_len]; exact hi), h0, Bool.false_or, hp, beq_self_eq_true,
        Bool.true_and]
  · exact CFSG.ONSchreier.allBelowN_iff.2 fun i hi => by simp [(PK_xs i hi).1]
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => CFSG.ONSchreier.allBelowN_iff.2
      fun j hj => ?_
    rcases Nat.lt_trichotomy i j with h | rfl | h
    · have hne : xs[i]! ≠ xs[j]! := fun e => dist j hj i h (XV_inj hi hj (by
        rw [← (PK_xs i hi).2, ← (PK_xs j hj).2, e]))
      simp [hne, Nat.ne_of_lt h]
    · simp
    · have hne : xs[i]! ≠ xs[j]! := fun e => dist i hi j h (XV_inj hj hi (by
        rw [← (PK_xs i hi).2, ← (PK_xs j hj).2, e]))
      simp [hne, Nat.ne_of_gt h]
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
    obtain ⟨a, b⟩ := hlt i hi
    rw [SJ_get (j := 0) (by omega), SJ_get (j := 1) (by omega), arrJ_get _ (PK_xs i hi).1,
      arrJ_get _ (PK_xs i hi).1, sL0, sL1,
      img_idx (k := 21) (by omega) mat_hJ1 (fun i hi => img 21 _ lp1a lp1b hi)
        (fun i hi => (hlt i hi).1) hi,
      img_idx (k := 22) (by omega) mat_hJ2 (fun i hi => img 22 _ lp2a lp2b hi)
        (fun i hi => (hlt i hi).2) hi]
    simp [a, b]

theorem lab_lt : allN 462 (fun k => Nat.blt (HNLab k) 4096) = true := by quickRfl

theorem lab_bit : allN 462 (fun k => Nat.beq (Nat.land (HNLab k) 1) 1) = true := by quickRfl

@[expose] def pop12 (m : ℕ) : ℕ := (List.range 12).foldl (fun acc i => acc + Nat.land (m >>> i) 1) 0

theorem lab_pop : allN 462 (fun k => Nat.beq (pop12 (HNLab k)) 6) = true := by quickRfl

theorem bit_eq (m i : ℕ) : Nat.land (m >>> i) 1 = if m.testBit i then 1 else 0 := by
  have e : Nat.land (m >>> i) 1 = (m >>> i) % 2 := Nat.and_one_is_mod _
  rw [e, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ i) with h | h <;> simp [h]

theorem popc12_eq (m : ℕ) : popc12 m = pop12 m := by
  have key : ∀ n, Nat.fold n (fun i _ acc => if m.testBit i then acc + 1 else acc) 0 =
      (List.range n).foldl (fun acc i => acc + Nat.land (m >>> i) 1) 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.fold_succ, ih, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        bit_eq]
      split_ifs <;> rfl
  exact key 12

theorem testBit0 {m : ℕ} (h : Nat.land m 1 = 1) : m.testBit 0 = true := by
  have e : m % 2 = 1 := by rw [← Nat.and_one_is_mod]; exact h
  simp [Nat.testBit_zero, e]

theorem lab_dist : allN 462 (fun k => allN k (fun j => Bool.not (Nat.beq (HNLab j) (HNLab k)))) =
    true := by quickRfl

theorem lab_perm : allN 462 (fun k =>
    Nat.beq (HNLab LocalData.lperm1[k]!) (canonMask (permMask (natArr LocalData.natGen1) (HNLab k))) &&
    Nat.beq (HNLab LocalData.lperm2[k]!) (canonMask (permMask (natArr LocalData.natGen2) (HNLab k)))) =
      true := by quickRfl

theorem neg_lab : Bool.not (Nat.beq (HNLab LocalData.lperm2[0]!)
    (canonMask (permMask (natArr LocalData.natGen1) (HNLab 0)))) = true := by quickRfl

theorem lab_ne {j k : ℕ} (hj : j < 462) (hk : k < 462) (h : j ≠ k) : HNLab j ≠ HNLab k := by
  intro e
  rcases Nat.lt_or_gt_of_ne h with h' | h'
  · have := allN_spec (allN_spec lab_dist k hk) j h'
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)
  · have := allN_spec (allN_spec lab_dist j hj) k h'
    rw [e, Nat.beq_refl] at this
    exact absurd this (by decide)

theorem label_ok : labelChecks = true := by
  obtain ⟨hlt, hl1, hl2⟩ := lperm_lt
  unfold labelChecks
  try dsimp only
  simp only [Bool.and_eq_true, and_assoc, beq_iff_eq]
  refine ⟨lab_size, hl1, hl2, ?_, ?_, ?_⟩
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun k hk => ?_
    have h1 : HNLab k < 4096 := by simpa [Nat.blt_eq] using allN_spec lab_lt k hk
    have h2 := Nat.eq_of_beq_eq_true (allN_spec lab_pop k hk)
    have h3 := testBit0 (Nat.eq_of_beq_eq_true (allN_spec lab_bit k hk))
    rw [lab_get hk, popc12_eq, h2, h3]
    simp [h1]
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun k hk => CFSG.ONSchreier.allBelowN_iff.2
      fun j hj => ?_
    rw [lab_get hk, lab_get hj]
    by_cases e : k = j
    · simp [e]
    · simp [e, lab_ne hk hj e]
  · refine CFSG.ONSchreier.allBelowN_iff.2 fun k hk => ?_
    obtain ⟨a, b⟩ := hlt k hk
    have := allN_spec lab_perm k hk
    rw [lab_get hk, lab_get a, lab_get b]
    simp only [Bool.and_eq_true] at this
    simp [a, b, Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2]

end CertificateChecks.KernelSporSch.HNLocal

end
