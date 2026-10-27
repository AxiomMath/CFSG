
module

public import Certificates.Kernel.Sporadic.Q3A.Glue3
public import CFSG.Sporadic.SuzRecog.Q3AGraphBase

public section

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.Q3A.Check
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Q3AK
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

theorem ds_parts {k : Nat} (hds : dsChk k = true) :
    countK 486 (fun t => Nat.beq (Nat.succ (vdK (actK (cA (rtK k)) (n0K t)))) (rdK k)) = dlK k ∧
    (∀ a, a + 1 < dlK k → posK k a < posK k (a + 1)) ∧
    ∀ a < dlK k, posK k a < 486 ∧ dsK k a = actK (cA (rtK k)) (n0K (posK k a)) ∧
      vdK (dsK k a) + 1 = rdK k := by
  unfold dsChk at hds
  rw [sB, sB, sB, band, band] at hds
  obtain ⟨h1, h2, h3⟩ := hds
  refine ⟨nbeq.1 h1, fun a ha => nblt.1 (allN_get h2 (by change a < dlK k - 1; omega)),
    fun a ha => ?_⟩
  have := allN_get h3 ha
  rw [sB, band, sB, band] at this
  obtain ⟨h4, h5, h6⟩ := this
  have e6 := nbeq.1 h6
  rw [← nbeq.1 h5] at e6
  exact ⟨nblt.1 h4, nbeq.1 h5, e6⟩

theorem vdK_lt {y : Nat} (h : vdK y ≠ 4) : y < 22880 := by
  rw [vdK_eq] at h
  by_contra hy
  exact h (ite_eq_right hy)

theorem isNbr0_vd (hv : ∀ i < 22880, vtOK i = true) (hf : ∀ i < 22880, frOK i = true) (y : Nat) :
    isNbr0 y = true ↔ vdK y = 1 := by
  rw [isNbr0_iff hv hf, vdK_one]

section Checks

variable (hv : ∀ i < 22880, vtOK i = true) (hf : ∀ i < 22880, frOK i = true)
  (hds : ∀ k < 3, dsChk k = true)
include hv hf

theorem any_nbrs {i : Nat} (hi : i < 22880) {p : Nat → Bool} :
    (nbrsOf i).any p = true ↔ ∃ t < 486, p (actK (cA i) (n0K t)) = true := by
  rw [nbrsOf_eq hv hf hi, List.any_toArray, List.any_map, List.any_eq_true]
  simp only [List.mem_range, Function.comp_apply]

theorem all_nbrs {i : Nat} (hi : i < 22880) {p : Nat → Bool} :
    (nbrsOf i).all p = true ↔ ∀ t < 486, p (actK (cA i) (n0K t)) = true := by
  rw [nbrsOf_eq hv hf hi, List.all_toArray, List.all_map, List.all_eq_true]
  simp only [List.mem_range, Function.comp_apply]

include hds

omit hv hf in
theorem dist202 : ∀ t < 486, vdK (actK (cA 202) (n0K t)) = 2 := by
  have h := all_of_count (ds_parts (hds 2 (by norm_num))).1
  intro t ht
  have : Nat.succ (vdK (actK (cA 202) (n0K t))) = 3 := nbeq.1 (h t ht)
  omega

theorem rootDist_vals : rootDist 0 = 0 ∧ rootDist 1 = 2 ∧ rootDist 2 = 2 ∧ rootDist 10 = 1 ∧
    rootDist 202 = 3 := by
  obtain ⟨-, -, h1, h2, -, h202⟩ := roots_parts
  have two : ∀ k < 2, rootDist (rtK k) = 2 := by
    intro k hk
    have hd := ds_parts (hds k (by omega))
    have hr : rtK k < 22880 := by obtain rfl | rfl : k = 0 ∨ k = 1 := (by omega) <;> decide
    have hfr : frootK (rtK k) = rtK k := by
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · exact h1
      · exact h2
    have hn : rtK k ≠ 0 ∧ rtK k ≠ 10 := by
      obtain rfl | rfl : k = 0 ∨ k = 1 := (by omega) <;> decide
    have hpos : 0 < dlK k := by obtain rfl | rfl : k = 0 ∨ k = 1 := (by omega) <;> decide
    obtain ⟨ht, hds0, hvd⟩ := hd.2.2 0 hpos
    have hrd : rdK k = 2 := by obtain rfl | rfl : k = 0 ∨ k = 1 := (by omega) <;> rfl
    rw [rootDist, ite_eq_right (by simpa using hn.1), not_nbr_root hv hf hfr hn.2]
    rw [ite_eq_right (by decide), ite_eq_left ((any_nbrs hv hf hr).2 ⟨_, ht, ?_⟩)]
    rw [isNbr0_vd hv hf, ← hds0]
    omega
  refine ⟨by rw [rootDist, ite_eq_left (by decide)], two 0 (by norm_num), two 1 (by norm_num),
    rootDist_10 hv hf, ?_⟩
  rw [rootDist, ite_eq_right (by decide), not_nbr_root hv hf h202 (by decide)]
  rw [ite_eq_right (by decide), ite_eq_right]
  rw [any_nbrs hv hf (by norm_num)]
  rintro ⟨t, ht, h⟩
  rw [isNbr0_vd hv hf, dist202 hds t ht] at h
  exact absurd h (by decide)

theorem rootDist_root {r : Nat} (hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 10 ∨ r = 202) :
    rootDist r = dK r := by
  obtain ⟨e0, e1, e2, e10, e202⟩ := rootDist_vals hv hf hds
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [e0]; rfl
  · rw [e1]; rfl
  · rw [e2]; rfl
  · rw [e10]; rfl
  · rw [e202]; rfl

theorem vDist_eq (y : Nat) : vDist y = vdK y := by
  unfold vDist
  rw [vdK_eq]
  by_cases hy : y < 22880
  · rw [ite_eq_left hy, ite_eq_left hy, froot_get hy]
    have hr := froot_root hf hy
    obtain ⟨hlt, hrr, -⟩ := fr_parts hf hy
    unfold distArr
    rw [getElem!_pos _ _ (by simpa using hlt), Array.getElem_map, Array.getElem_range,
      froot_get hlt, hrr, beq_self_eq_true, ite_eq_left rfl, rootDist_root hv hf hds hr]
  · rw [ite_eq_right hy, ite_eq_right hy]

theorem rootDist_rt {k : Nat} (hk : k < 3) : rootDist (rtK k) = rdK k := by
  obtain ⟨-, e1, e2, -, e202⟩ := rootDist_vals hv hf hds
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  · exact e1
  · exact e2
  · exact e202

omit hv hf hds in
theorem rt_lt {k : Nat} (hk : k < 3) : rtK k < 22880 := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := (by omega) <;> decide

theorem downSet_eq {k : Nat} (hk : k < 3) :
    downSet (rtK k) = ((List.range (dlK k)).map (dsK k)).toArray := by
  obtain ⟨hc, hs, hm⟩ := ds_parts (hds k hk)
  unfold downSet
  rw [nbrsOf_eq hv hf (rt_lt hk)]
  apply Array.ext'
  rw [Array.toList_filter, List.toList_toArray, List.toList_toArray, List.filter_map]
  have hfil : (List.range 486).filter ((fun y => vDist y + 1 == rootDist (rtK k)) ∘
      fun t => actK (cA (rtK k)) (n0K t)) = (List.range (dlK k)).map (posK k) := by
    rw [List.filter_congr (q := fun t => Nat.beq (Nat.succ (vdK (actK (cA (rtK k)) (n0K t))))
        (rdK k)) fun t _ => by
      rw [Function.comp_apply, vDist_eq hv hf hds, rootDist_rt hv hf hds hk, beqN]]
    refine filter_range_eq (pairwise_of_succ hs) (fun x hx => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      have ha' := List.mem_range.1 ha
      obtain ⟨h1, h2, h3⟩ := hm a ha'
      refine ⟨h1, nbeq.2 ?_⟩
      rw [← h2]
      exact h3
    · rw [← countK_eq, hc, List.length_map, List.length_range]
  rw [hfil, List.map_map]
  refine List.map_congr_left fun a ha => ?_
  exact ((hm a (List.mem_range.1 ha)).2.1).symm

omit hv hf in
theorem ds_lt {k a : Nat} (hk : k < 3) (ha : a < dlK k) : dsK k a < 22880 := by
  have h := ((ds_parts (hds k hk)).2.2 a ha).2.2
  refine vdK_lt fun e => ?_
  rw [e] at h
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := (by omega) <;> exact absurd h (by decide)

omit hf hds in
theorem vertOK_true : vertOK = true := by
  unfold vertOK
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true,
    decide_eq_true_eq, and_assoc]
  refine ⟨pRhoI.2, fix0_size, ?_, fun s hs => (pBAi hs).2, ?_, tpar_size, tlab_size, ?_,
    fun i hi => ⟨?_, ?_⟩⟩
  · rw [eqA_P (p_comp pRho (p_comp pRho pRho)) pidn_P]
    exact kRho3
  · unfold fimg
    rw [Array.size_map, Array.size_range]
  · rw [fimg_get (by norm_num), fimgAt_eq, ite_eq_right (by omega)]
  · rw [keyIdx_eq hv, keyOf_FL (fimg_FL hv hi)]
    exact (vt_parts hv hi).2.1
  · by_cases h0 : i = 0
    · exact Or.inl h0
    · right
      obtain ⟨hp, hl, -⟩ := (vt_parts hv hi).1 h0
      have hp' : tpar[i]! < i := by rw [tpar_get hi]; exact hp
      refine ⟨hp', by rw [tlab_get hi]; exact hl, ?_⟩
      rw [fimg_get hi, fimg_get (by omega), fimgAt_eq, ite_eq_left ⟨by omega, hp'⟩]

omit hds in
theorem forestOK_true : forestOK = true := by
  unfold forestOK
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, decide_eq_true_eq,
    and_assoc]
  refine ⟨fun s hs => ⟨(pXI hs).2, ?_, ?_⟩, froot_size, fpar_size, flab_size, fdep_size,
    fun i hi => ?_⟩
  · rw [eqA_P (p_comp (pX hs) pRho) (p_comp pRho (pX hs))]
    obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
    · have h := kX0
      rw [band] at h
      rw [XK0]
      exact h.1
    · have h := kX1
      rw [band] at h
      rw [XK1]
      exact h.1
  · rw [OddCore.inM_eq (pX hs).1 (pX hs).2]
    obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
    · have h := kX0
      rw [band] at h
      rw [XK0]
      exact h.2
    · have h := kX1
      rw [band] at h
      rw [XK1]
      exact h.2
  · obtain ⟨h1, h2, h3, h4⟩ := fr_parts hf hi
    rw [froot_get hi, froot_get h1, h2]
    refine ⟨h1, rfl, ?_⟩
    by_cases hr : frootK i = i
    · rw [ite_eq_left (by simpa using hr), fdep_get hi, h3 hr]
      rfl
    · rw [ite_eq_right (by simpa using hr)]
      obtain ⟨p1, p2, p3, p4, p5⟩ := h4 hr
      rw [fpar_get hi, flab_get hi, fdep_get hi, fdep_get p1, froot_get p1,
        CFSG.Sporadic.SuzRecog.Q3A.xTab_get p2 p1,
        actIdx_eq hv (pX p2) p1, p4, p5]
      simp [p1, p2, p3]

omit hds in
theorem nbrOrbOK_true : nbrOrbOK = true := by
  unfold nbrOrbOK
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro k hk
  have hn := n0_parts.2.2 0 (by norm_num)
  have h0 : nbr0[0]! = n0K 0 := by
    rw [nbr0_eq hv hf, getElem!_pos _ 0 (by simp), List.getElem_toArray, List.getElem_map,
      List.getElem_range]
  rw [h0, froot_get hn.1, hn.2]
  cases h : isNbr0 k
  · rfl
  · rw [froot_get hk, ((isNbr0_iff hv hf k).1 h).2]
    rfl

omit hv hf hds in
theorem roots_all {f : Nat → Bool} (h0 : f 0 = true) (h1 : f 1 = true) (h2 : f 2 = true)
    (h10 : f 10 = true) (h202 : f 202 = true) : roots.all f = true := by
  rw [roots_eq, Array.all_eq_true']
  intro r hr
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem distOK_true : distOK = true := by
  obtain ⟨e0, e1, e2, e10, e202⟩ := rootDist_vals hv hf hds
  unfold distOK
  refine roots_all ?_ ?_ ?_ ?_ ?_
  · rw [e0]; rfl
  · rw [e1]; rfl
  · rw [e2]; rfl
  · rw [e10]; rfl
  · rw [e202, Bool.or_eq_true]
    right
    rw [any_nbrs hv hf (by norm_num)]
    exact ⟨0, by norm_num, by rw [vDist_eq hv hf hds, dist202 hds 0 (by norm_num)]; rfl⟩

theorem layer3OK_true : layer3OK = true := by
  obtain ⟨e0, e1, e2, e10, e202⟩ := rootDist_vals hv hf hds
  unfold layer3OK
  refine roots_all ?_ ?_ ?_ ?_ ?_
  · rw [e0]; rfl
  · rw [e1]; rfl
  · rw [e2]; rfl
  · rw [e10]; rfl
  · rw [e202, Bool.or_eq_true]
    right
    rw [all_nbrs hv hf (by norm_num)]
    intro t ht
    rw [vDist_eq hv hf hds, dist202 hds t ht]
    rfl

omit hv hf hds in
theorem hasChild_of {k a b : Nat} (hb : b < dlK k) (h0 : b ≠ 0) (ha : parK k b = a) :
    hasChild k a = true := by
  unfold hasChild
  cases h : allN (dlK k) (fun b => Bool.not (bAnd(Bool.not (Nat.beq b 0), Nat.beq (parK k b) a)))
  · rfl
  · have := allN_get h hb
    rw [nbeq_false h0, ha, Nat.beq_refl] at this
    exact absurd this (by decide)

omit hv hf hds in
theorem ci_eq {k a : Nat} (hci : ciSl k a = true) (hg : k < 2 ∨ hasChild k a = true) :
    ciK k a = cIA (dsK k a) := by
  unfold ciSl at hci
  rw [bIf_eq, ite_eq_left] at hci
  · exact nbeq.1 hci
  · rw [bIf_eq]
    rcases hg with hg | hg
    · rw [ite_eq_left (nblt.2 hg)]
    · split_ifs
      · rfl
      · exact hg

theorem adjIdx_ds {k a b : Nat} (hk : k < 3) (ha : a < dlK k) (hb : b < dlK k) :
    adjIdx (dsK k a) (dsK k b) = adjK (cIA (dsK k a)) (dsK k b) := by
  unfold adjIdx
  rw [actIdx_eq hv (p_cArrInv hv (ds_lt hds hk ha)) (ds_lt hds hk hb)]
  rw [Bool.eq_iff_iff, isNbr0_iff hv hf, adjK_iff]

omit hv hf hds in
theorem spanPin_rt {k : Nat} (hk : k < 3) : spanPin (rtK k) =
    (hexTable 4 (dlK k) (soK k) CFSG.Sporadic.SuzRecog.Q3AVtxData.spanHex,
      hexTable 4 (dlK k) (soK k + dlK k) CFSG.Sporadic.SuzRecog.Q3AVtxData.spanHex) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := (by omega) <;> rfl

theorem span_ok {k : Nat} (hk : k < 3) (hci : ∀ a < dlK k, ciSl k a = true)
    (hsp : ∀ a < dlK k, spSl k a = true) :
    spanCheck (downSet (rtK k)) (spanPin (rtK k)) = true := by
  have hn : dlK k ≤ 486 := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := (by omega) <;> decide
  have hso : soK k + dlK k + dlK k ≤ 1016 := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := (by omega) <;> decide
  have hD : (downSet (rtK k)).size = dlK k := by
    rw [downSet_eq hv hf hds hk, List.size_toArray, List.length_map, List.length_range]
  have hDg : ∀ a < dlK k, (downSet (rtK k))[a]! = dsK k a := fun a ha => by
    rw [downSet_eq hv hf hds hk, getElem!_pos _ a (by simpa using ha), List.getElem_toArray,
      List.getElem_map, List.getElem_range]
  have hsh : ∀ b < dlK k, b ≠ 0 → parK k b < dlK k ∧ depK k (parK k b) < depK k b := by
    intro b hb h0
    have := allN_get (allN_get kShape hk) hb
    rw [bIf_eq, ite_eq_right (by rw [nbeq]; exact h0), sB, band] at this
    exact ⟨nblt.1 this.1, nblt.1 this.2⟩
  unfold spanCheck
  rw [spanPin_rt hk]
  simp only [Bool.and_eq_true, beq_iff_eq, CFSG.Monster.B.Co2.allLt_iff, Bool.or_eq_true,
    decide_eq_true_eq, hexTable_size, hD]
  refine ⟨⟨trivial, trivial⟩, fun b hb => ?_⟩
  by_cases h0 : b = 0
  · exact Or.inl h0
  right
  obtain ⟨hp, hdep⟩ := hsh b hb h0
  have e1 : (hexTable 4 (dlK k) (soK k) CFSG.Sporadic.SuzRecog.Q3AVtxData.spanHex)[b]! =
      parK k b := span_get hb (by omega)
  have e2 : ∀ c < dlK k, (hexTable 4 (dlK k) (soK k + dlK k)
      CFSG.Sporadic.SuzRecog.Q3AVtxData.spanHex)[c]! = depK k c := fun c hc => span_get hc (by omega)
  rw [e1, e2 _ hp, e2 _ hb, hDg _ hp, hDg _ hb, adjIdx_ds hv hf hds hk hp hb]
  refine ⟨⟨hp, hdep⟩, ?_⟩
  have hc := hasChild_of hb h0 rfl
  rw [← ci_eq (hci _ hp) (Or.inr hc)]
  have h := hsp _ hp
  unfold spSl at h
  rw [bIf_eq, ite_eq_left hc, sB] at h
  have := allN_get h hb
  rw [bIf_eq, ite_eq_left] at this
  · exact this
  · rw [band, nbeq]
    exact ⟨by rw [nbeq_false h0]; rfl, rfl⟩

theorem spanOK_true (hci : ∀ k < 3, ∀ a < dlK k, ciSl k a = true)
    (hsp : ∀ k < 3, ∀ a < dlK k, spSl k a = true) : spanOK = true := by
  obtain ⟨e0, -, -, e10, -⟩ := rootDist_vals hv hf hds
  unfold spanOK
  refine roots_all ?_ ?_ ?_ ?_ ?_
  · rw [e0]; rfl
  · rw [Bool.or_eq_true]
    exact Or.inr (span_ok hv hf hds (k := 0) (by norm_num) (hci 0 (by norm_num))
      (hsp 0 (by norm_num)))
  · rw [Bool.or_eq_true]
    exact Or.inr (span_ok hv hf hds (k := 1) (by norm_num) (hci 1 (by norm_num))
      (hsp 1 (by norm_num)))
  · rw [e10]; rfl
  · rw [Bool.or_eq_true]
    exact Or.inr (span_ok hv hf hds (k := 2) (by norm_num) (hci 2 (by norm_num))
      (hsp 2 (by norm_num)))

end Checks

end CertificateChecks.KernelSpor.Q3AG

end
