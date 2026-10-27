module

public import Certificates.Kernel.U38R.Glue
public import Certificates.Kernel.U38R.ElimChecks
public import CFSG.Certificates.Kernel.U38ElimSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38R

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.K426K CFSG.KC.B3S3K
  CFSG.KC.Misc.ArrEnum CFSG.KC.U38Elim
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec18.Item185Proof.U38Elim CFSG.RankThree.PartTwo.Sec4.Item434U38
open CFSG.Monster.B.Co2 (allLt_iff)

theorem bAnd_iff' {a b : Bool} :
    Bool.rec (motive := fun _ => Bool) false b a = true ↔ a = true ∧ b = true := by
  cases a <;> simp

theorem bIf_mp {c t : Bool} (h : Bool.rec (motive := fun _ => Bool) true t c = true)
    (hc : c = true) : t = true := by
  subst hc
  exact h

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem beq_nat (a b : Nat) : (a == b) = Nat.beq a b := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq]
  exact ⟨fun h => h ▸ Nat.beq_refl a, Nat.eq_of_beq_eq_true⟩

theorem lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem mulK_lt {i j : ℕ} (hi : i < 729) (hj : j < 729) : mulK i j < 729 := by
  have h := tabOK_R
  unfold tabOK at h
  rw [allLt_iff] at h
  have h2 := h i (by rw [enumR.2.1]; exact hi)
  rw [allLt_iff] at h2
  have h3 := h2 j (by rw [enumR.2.1]; exact hj)
  rw [Bool.and_eq_true, decide_eq_true_eq, mulI_R hi hj, enumR.2.1] at h3
  exact h3.1

theorem commI_R {i j : ℕ} (hi : i < 729) (hj : j < 729) :
    commI (mulTab (rCert ()).pts) i j = eComm i j := by
  unfold commI eComm
  rw [mulI_R hi hj, mulI_R hj hi, beq_nat]

theorem cubeI_R {i : ℕ} (hi : i < 729) : cubeI (mulTab (rCert ()).pts) i = eCube i := by
  unfold cubeI eCube
  rw [mulI_R hi hi, mulI_R hi (mulK_lt hi hi), beq_nat]

theorem belems_R {i1 i2 : ℕ} (h1 : i1 < 729) (h2 : i2 < 729) :
    belems (mulTab (rCert ()).pts) i1 i2 = eBel i1 i2 := by
  simp only [belems, eBel]
  rw [mulI_R h1 h1, mulI_R h2 h2, mulI_R h1 h2, mulI_R (mulK_lt h1 h1) h2,
    mulI_R h1 (mulK_lt h2 h2), mulI_R (mulK_lt h1 h1) (mulK_lt h2 h2)]

theorem eBel_lt {i1 i2 : ℕ} (h1 : i1 < 729) (h2 : i2 < 729) : ∀ b ∈ eBel i1 i2, b < 729 := by
  have a := mulK_lt h1 h1
  have b := mulK_lt h2 h2
  have c := mulK_lt h1 h2
  have d := mulK_lt a h2
  have e := mulK_lt h1 b
  have f := mulK_lt a b
  intro x hx
  simp only [eBel, List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

theorem S3_mem {i : ℕ} (hi : i < 729) (hx : eX i = true) (h0 : i ≠ 0) (hc : eCube i = true) :
    i ∈ S3L := by
  have h := Orb.allN_iff.1 e185S3 i hi
  refine (eMem_iff _ _).1 (bIf_mp h ?_)
  rw [bAnd_iff', bAnd_iff', beqF h0]
  exact ⟨hx, rfl, hc⟩

theorem S3_in {s : ℕ} (hs : s ∈ S3L) : s < 729 ∧ eX s = true := by
  have h : Bool.rec (motive := fun _ => Bool) false (eX s) (Nat.blt s 729) = true :=
    (eAll_iff _ _).1 e185S3In s hs
  rw [bAnd_iff'] at h
  exact ⟨lt_of_blt h.1, h.2⟩

theorem CM_bit {i : ℕ} (hi : i ∈ S3L) {x : ℕ} (hx : x < 729) : eBit (CM i) x = eComm x i := by
  have h : allN 729 (fun x =>
      Bool.rec (motive := fun _ => Bool) (!(eBit (CM i) x)) (eBit (CM i) x) (eComm x i)) = true :=
    (eAll_iff _ _).1 e185CM i hi
  have h2 := Orb.allN_iff.1 h x hx
  cases hc : eComm x i <;> simp only [hc] at h2 <;> simpa using h2

theorem d1_wit {j : ℕ} (hj : j < 729) (hx : eX j = false) : ∃ s ∈ S3L, eBit (CM s) j = false := by
  have h := Orb.allN_iff.1 e185D1 j hj
  simp only [hx] at h
  obtain ⟨s, hs, h2⟩ := (eAny_iff _ _).1 h
  exact ⟨s, hs, by simpa using h2⟩

theorem pair_facts {i1 i2 : ℕ} (h1 : i1 ∈ S3L) (h2 : i2 ∈ S3L) (hc : eBit (CM i2) i1 = true)
    (hn1 : i2 ≠ i1) (hn2 : i2 ≠ mulK i1 i1) :
    (CM i1 &&& CM i2) = CN (pg 4 15 (PK i1) i2) ∧
      ∀ t < 9, eBK BK (pg 4 15 (PK i1) i2) t ∈ eBel i1 i2 := by
  have h := (eAll_iff _ _).1 ((eAll_iff _ _).1 e185Pairs i1 h1) i2 h2
  have h' := bIf_mp h (by rw [bAnd_iff', bAnd_iff', beqF hn1, beqF hn2]; exact ⟨hc, rfl, rfl⟩)
  unfold e185PairK at h'
  rw [strictB_eq', bAnd_iff'] at h'
  exact ⟨Nat.eq_of_beq_eq_true h'.1, fun t ht => (eMem_iff _ _).1 (Orb.allN_iff.1 h'.2 t ht)⟩

theorem pg4_lt (v i : ℕ) : pg 4 15 v i < 16 := by
  unfold pg
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem key_facts {k j : ℕ} (hk : k < 16) (hj : j < 729) (hb : eBit (CN k) j = true)
    (hx : eX j = false) (hc : eCube j = true) :
    (∃ b, (∃ t < 9, eBK BK k t = b) ∧
        ∀ x < 729, eBit (CN k) x = true → mulK x j ≠ mulK (mulK b j) x) ∨
      (j ∈ e185WJ ∧ ∀ l ∈ e185WL, ∃ t < 9, eBK BK k t = l) := by
  have h := Orb.allN_iff.1 (Orb.allN_iff.1 e185Keys k hk) j hj
  have h' := bIf_mp h (by rw [bAnd_iff', bAnd_iff', hx]; exact ⟨hb, rfl, hc⟩)
  rw [strictB_eq'] at h'
  generalize pg 4 15 (TW k) j = t at h'
  cases ht : Nat.blt t 9
  · rw [ht] at h'
    unfold e185OmK at h'
    rw [bAnd_iff'] at h'
    refine Or.inr ⟨(eMem_iff _ _).1 h'.1, fun l hl => ?_⟩
    obtain ⟨t', ht', e⟩ := (eAnyN_iff _ _).1 ((eAll_iff _ _).1 h'.2 l hl)
    exact ⟨t', ht', Nat.eq_of_beq_eq_true e⟩
  · rw [ht] at h'
    unfold e185RefK at h'
    rw [strictB_eq'] at h'
    refine Or.inl ⟨eBK BK k t, ⟨t, lt_of_blt ht, rfl⟩, fun x hx hbx e => ?_⟩
    have h2 := bIf_mp (Orb.allN_iff.1 h' x hx) hbx
    rw [e, Nat.beq_refl] at h2
    exact absurd h2 Bool.false_ne_true

theorem PT {i : ℕ} (hi : i < 729) : PP 513 10 (UR.T i) := PP_pts UR.ok pG i (by rw [hN]; exact hi)

theorem witOK_of_witK {hi j : ℕ} (hj : j < 729) (h : witK hi j = true) :
    witOK (rCert ()).pts (hList ()) hi j = true := by
  unfold witK at h
  simp only [strictB_eq', bAnd_iff'] at h
  obtain ⟨hh, hc, h1, h2, h3, h4⟩ := h
  have hi9 : hi < 9 := lt_of_blt hh
  have pH : PP 513 10 (RH.F (3 + hi)) := pp_of_permB kW (pRH (by omega))
  have pA := PT (by norm_num : 247 < 729)
  have pB := PT (by norm_num : 263 < 729)
  have pC := PT (by norm_num : 282 < 729)
  have pJ := PT hj
  have eA : conjA 513 (unpack 513 10 (RH.F (3 + hi))) (unpack 513 10 (UR.T 247)) =
      unpack 513 10 (eCj (RH.F (3 + hi)) (UR.T 247)) := by
    rw [conjA, invCand_PP pH, compA_PP pA pH.inv, compA_PP pH (pA.mul pH.inv)]
    rfl
  have eB : conjA 513 (unpack 513 10 (RH.F (3 + hi))) (unpack 513 10 (UR.T 263)) =
      unpack 513 10 (eCj (RH.F (3 + hi)) (UR.T 263)) := by
    rw [conjA, invCand_PP pH, compA_PP pB pH.inv, compA_PP pH (pB.mul pH.inv)]
    rfl
  have cA : PP 513 10 (eCj (RH.F (3 + hi)) (UR.T 247)) := pH.mul (pA.mul pH.inv)
  have cB : PP 513 10 (eCj (RH.F (3 + hi)) (UR.T 263)) := pH.mul (pB.mul pH.inv)
  have z1 : PP 513 10 (pcomp 513 10 (mask 10) (eCj (RH.F (3 + hi)) (UR.T 247)) (UR.T 263)) :=
    cA.mul pB
  have z2' : PP 513 10 (pcomp 513 10 (mask 10) (eCj (RH.F (3 + hi)) (UR.T 263)) (UR.T 282)) :=
    cB.mul pC
  have z2 : PP 513 10 (pcomp 513 10 (mask 10) (UR.T 247)
      (pcomp 513 10 (mask 10) (eCj (RH.F (3 + hi)) (UR.T 263)) (UR.T 282))) :=
    pA.mul z2'
  have pp := z1.mul z2
  unfold witOK
  simp only []
  rw [hList_get hi9, E_get (by norm_num : 247 < 729), E_get (by norm_num : 263 < 729),
    E_get (by norm_num : 282 < 729), E_get hj, hList_size, eA, eB, compA_PP cA pB,
    compA_PP cB pC, compA_PP pA z2', compA_PP z1 z2, compA_PP pH pJ, compA_PP pJ pH,
    eqA_PP (pH.mul pJ) (pJ.mul pH), compA_PP z1 z1, compA_PP (z1.mul z1) (z1.mul z1),
    compA_PP z2 z2, compA_PP (z2.mul z2) (z2.mul z2), compA_PP pp pp, compA_PP pp (pp.mul pp),
    idA_eq kW, eqA_PP ((z1.mul z1).mul (z1.mul z1)) (PP.id kW),
    eqA_PP ((z2.mul z2).mul (z2.mul z2)) (PP.id kW), eqA_PP (pp.mul (pp.mul pp)) (PP.id kW),
    eqA_PP pp (PP.id kW)]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hi9, hc⟩, h1⟩, h2⟩, h3⟩, h4⟩

theorem wPairs_eq : wPairs = (List.range 18).map fun m => (e185WJ.getD m 0, m / 2) := by decide

theorem wit_R : ∀ w ∈ wPairs, witOK (rCert ()).pts (hList ()) w.2 w.1 = true := by
  intro w hw
  rw [wPairs_eq, List.mem_map] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  rw [List.mem_range] at hm
  have hj : e185WJ.getD m 0 < 729 := by
    have hl : ∀ j ∈ e185WJ, j < 729 := by decide
    have hlen : m < e185WJ.length := by simpa [e185WJ] using hm
    rw [List.getD_eq_getElem _ _ hlen]
    exact hl _ (List.getElem_mem hlen)
  exact witOK_of_witK hj (Orb.allN_iff.1 e185Wit m hm)

theorem wj_mem {j : ℕ} (h : j ∈ e185WJ) : ∃ w ∈ wPairs, w.1 = j := by
  have h' : j ∈ wPairs.map Prod.fst := by
    have e : wPairs.map Prod.fst = e185WJ := by decide
    rw [e]
    exact h
  obtain ⟨w, hw, e⟩ := List.mem_map.1 h'
  exact ⟨w, hw, e⟩

theorem d1_R : d1OK (mulTab (rCert ()).pts) (inXArr (rawLevels 513 strong3 base3) (rCert ()).pts)
    (rCert ()).pts.size = true := by
  simp only [d1OK, enumR.2.1]
  rw [allLt_iff]
  intro j hj
  rw [inX_get hj]
  cases hx : Nat.beq (ixBit j) 1
  · obtain ⟨s, hs, hb⟩ := d1_wit hj hx
    obtain ⟨hs1, hs2⟩ := S3_in hs
    rw [Bool.false_or, List.any_eq_true]
    refine ⟨s, ?_, ?_⟩
    · unfold flagged
      rw [List.mem_filter, List.mem_range, inX_get hs1]
      exact ⟨hs1, hs2⟩
    · rw [commI_R hj hs1, ← CM_bit hs hj, hb]
      rfl
  · rfl

theorem triples_R : triplesOK (rCert ()).pts (hList ()) (mulTab (rCert ()).pts)
    (inXArr (rawLevels 513 strong3 base3) (rCert ()).pts) = true := by
  simp only [triplesOK, enumR.2.1, List.all_eq_true, List.mem_filter, List.mem_range]
  intro i1 ⟨hi1, q1⟩ i2 ⟨hi2, q2⟩
  rw [inX_get hi1, cubeI_R hi1, Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne] at q1
  rw [inX_get hi2, cubeI_R hi2, Bool.and_eq_true, Bool.and_eq_true, bne_iff_ne] at q2
  have m1 := S3_mem hi1 q1.1.1 q1.1.2 q1.2
  have m2 := S3_mem hi2 q2.1.1 q2.1.2 q2.2
  rw [commI_R hi1 hi2, mulI_R hi1 hi1]
  by_cases hg : (eComm i1 i2 && i2 != i1 && i2 != mulK i1 i1) = true
  swap
  · rw [Bool.not_eq_true] at hg
    rw [hg]
    rfl
  rw [hg, Bool.not_true, Bool.false_or, List.all_eq_true]
  simp only [Bool.and_eq_true, bne_iff_ne] at hg
  obtain ⟨⟨hcm, hne1⟩, hne2⟩ := hg
  have hcm' : eBit (CM i2) i1 = true := by rw [CM_bit m2 hi1]; exact hcm
  obtain ⟨hk, hbel⟩ := pair_facts m1 m2 hcm' hne1 hne2
  intro j hjm
  rw [List.mem_filter, List.mem_range] at hjm
  obtain ⟨hj, qj⟩ := hjm
  rw [inX_get hj, cubeI_R hj, Bool.and_eq_true, Bool.not_eq_true'] at qj
  rw [commI_R hj hi1, commI_R hj hi2]
  by_cases hc : (eComm j i1 && eComm j i2) = true
  swap
  · rw [Bool.not_eq_true] at hc
    rw [hc]
    rfl
  rw [hc, Bool.not_true, Bool.false_or]
  have hbj : eBit (CN (pg 4 15 (PK i1) i2)) j = true := by
    rw [← hk, eBit_land, CM_bit m1 hj, CM_bit m2 hj]
    exact hc
  rcases key_facts (pg4_lt _ _) hj hbj qj.1 qj.2 with ⟨b, ⟨t, ht, hbt⟩, hb⟩ | ⟨hjw, hl⟩
  · have hbm : b ∈ eBel i1 i2 := by rw [← hbt]; exact hbel t ht
    have hb729 : b < 729 := eBel_lt hi1 hi2 b hbm
    rw [Bool.or_eq_true]
    left
    unfold refD2
    rw [List.any_eq_true]
    refine ⟨b, by rw [belems_R hi1 hi2]; exact hbm, ?_⟩
    rw [List.all_eq_true]
    intro x hxm
    unfold cenOf at hxm
    rw [List.mem_filter, List.mem_range] at hxm
    obtain ⟨hx, hxc⟩ := hxm
    rw [commI_R hx hi1, commI_R hx hi2] at hxc
    have hbx : eBit (CN (pg 4 15 (PK i1) i2)) x = true := by
      rw [← hk, eBit_land, CM_bit m1 hx, CM_bit m2 hx]
      exact hxc
    rw [mulI_R hx hj, mulI_R hb729 hj, mulI_R (mulK_lt hb729 hj) hx, bne_iff_ne]
    exact hb x hx hbx
  · rw [Bool.or_eq_true]
    right
    unfold omegaOK
    rw [List.any_eq_true]
    obtain ⟨w, hw, hw1⟩ := wj_mem hjw
    refine ⟨w, hw, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
    refine ⟨⟨hw1, fun l hl' => ?_⟩, ?_⟩
    · obtain ⟨t, ht, e⟩ := hl l hl'
      have hm : l ∈ belems (mulTab (rCert ()).pts) i1 i2 := by
        rw [belems_R hi1 hi2, ← e]
        exact hbel t ht
      simpa using hm
    · rw [← hw1]
      exact wit_R w hw

theorem check_R : check () = true := by
  unfold check checkWith
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨enumR.1, enumR.2.1⟩, genOK_R⟩, tabOK_R⟩, flagged_R⟩, hsOK_R⟩, d1_R⟩, triples_R⟩

end CertificateChecks.KernelU38R

end
