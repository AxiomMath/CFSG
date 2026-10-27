
module

public import Certificates.Kernel.SporSch.Co2M.ThirdGlueBase

public import CFSG.Certificates.Kernel.SporSch.OrbitTrSound
public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1
public import CFSG.Certificates.Kernel.SporSch.ThirdChainHBase

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Co2M CFSG.KS.Co2Third
open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

theorem S3_size : S3.size = 30 := by
  rw [extendArrs_size, aArrs_size, ds_facts.1]

theorem t3T_len : t3T.length = 30 := by rw [← t3_rep.1, S3_size]

theorem S3_get {k : ℕ} (hk : k < 30) : S3[k]! = unpack 2300 12 (Co2T3.S k) := by
  have h1 := (MatRep.repT_get t3_rep (by rw [t3T_len]; exact hk)).1
  have h2 := (bindK_sound good V_size (fun i hi => V_get hi) rfl (bind_t3 hk)).1
  rw [h1, ← h2]

theorem binds : Binds 2300 12 Co2T3.S 30 13 Co2T3.BP S3 thB :=
  ⟨by norm_num, by norm_num, by norm_num, S3_size, fun _ hj => S3_get hj, thB_size',
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec base_ok t ht)⟩

theorem S3_inv {j : ℕ} (hj : j < S3.size) : isInvA 2300 S3[j]! (invCand 2300 S3[j]!) = true := by
  have := isInv_of binds perm_ok j hj
  have e : (rawInvs 2300 S3)[j]! = invCand 2300 S3[j]! := by
    rw [rawInvs, getElem!_pos _ j (by simpa using hj), Array.getElem_map, getElem!_pos S3 j hj]
  rwa [e] at this

theorem allInv_S3 : allInv S3 = true := allLt_iff.2 fun _ hj => S3_inv hj

theorem rep_S3 {j : ℕ} (hj : j < 30) : Rep 2300 S3[j]! (permOfArr 2300 S3[j]!) :=
  (rep_permOfArr (S3_inv (by rw [S3_size]; exact hj))).1

theorem S3_mem {j : ℕ}
    (hj : j < 30) : permOfArr 2300 S3[j]! ∈ co2P := by
  have hT : RepTuple 2300 S3 (extendTuple aSeeds witRec.third.strongDerivations) :=
    repTuple_a.extend (by rw [aSeeds_length]; exact ds_facts.2.2.1) allInv_S3
  have hl : j < (extendTuple aSeeds witRec.third.strongDerivations).length := by
    rw [extendTuple_length, aSeeds_length, ds_facts.1]
    omega
  rw [Rep.unique (rep_S3 hj) (hT.rep hl)]
  exact extendTuple_mem co2P aSeeds _ aSeeds_mem _ (getD_mem hl)

theorem step_rep {j : ℕ}
    (hj : j ≤ 13) {s : Array ℕ} (hs : s ∈ thirdSteps S3 thB j) : ∃ g ∈ stabB j, Rep 2300 s g := by
  obtain ⟨i, hi, hf, hs⟩ := mem_thirdSteps_iff.1 hs
  rw [S3_size] at hi
  have hfix := fix_of_fixesFirst (rep_S3 hi) hj hf
  rcases hs with rfl | rfl
  · exact ⟨_, ⟨S3_mem hi, hfix⟩, rep_S3 hi⟩
  · refine ⟨_, ⟨co2P.inv_mem (S3_mem hi), fun t ht => ?_⟩, rep_invCand (rep_S3 hi)⟩
    rw [Equiv.Perm.inv_eq_iff_eq, hfix t ht]

theorem Gj_le {j : ℕ} (hj : j ≤ 13) :
    Gj j ≤ stabB j := by
  rw [Gj, Subgroup.closure_le]
  rintro g ⟨s, hs, hg⟩
  obtain ⟨g', hg', hr⟩ := step_rep hj hs
  rw [Rep.unique hg hr]
  exact hg'

theorem step_mem_Gj {j : ℕ}
    (hj : j ≤ 13) {s : Array ℕ} (hs : s ∈ thirdSteps S3 thB j) : ∃ g ∈ Gj j, Rep 2300 s g := by
  obtain ⟨g, -, hg⟩ := step_rep hj hs
  exact ⟨g, Subgroup.subset_closure ⟨s, hs, hg⟩, hg⟩

theorem lvFacts {j : ℕ}
    (hj : j < 13) : OrbTr.Facts (Gj j) (thirdSteps S3 thB j) thB[j]! thL[j]! := by
  rw [thL_get hj]
  exact OrbTr.orbitTr_facts (Gj j) _ (thB_lt' hj) fun t ht =>
    step_mem_Gj hj.le (by rw [getElem!_pos _ t ht]; exact Array.getElem_mem ht)

theorem stepsK {j : ℕ} (hj : j ≤ 13) :
    stCnt (t3St j) = (rawSteps 2300 S3 thB j).size ∧
      ∀ l < (rawSteps 2300 S3 thB j).size, ∀ p < 2300,
        pg 12 (mask 12) (letterK Co2T3.S Co2T3.SI 30 (stAt (t3St j) l)) p =
          ((rawSteps 2300 S3 thB j)[l]!)[p]! :=
  steps_eq binds perm_ok (by norm_num) hj fun t ht => thB_lt' ht

theorem size_eq_rcnt {j : ℕ}
    (hj : j < 13) : thL[j]!.pts.size = rcnt (Co2T3.LR j) := by
  have F := lvFacts hj
  have R := recF hj
  obtain ⟨hcnt, hstep⟩ := stepsK hj.le
  set st := thirdSteps S3 thB j
  have hst : ∀ s ∈ st, ∀ p < 2300, s[p]! < 2300 := fun s hs p hp => by
    obtain ⟨g, -, hg⟩ := step_mem_Gj hj.le hs
    exact hg.lt hp
  refine len_eq_of_orbit (r := st.size) (P := fun k => thL[j]!.pts[k]!)
    (Q := fun k => rpt 12 (mask 12) (Co2T3.LR j) k) (F := fun t p => (st[t]!)[p]!) F.pos R.c_pos
    ?_ F.inj ?_ ?_ ?_ ?_ ?_
  · rw [F.root, R.root, Nat.eq_of_beq_eq_true (allN_spec base_ok j hj)]
  · intro a ha b hb e
    rw [← (R.pt a ha).2, ← (R.pt b hb).2]
    exact congrArg _ e
  · intro k hk hk0
    obtain ⟨h, hh, s, hs, e⟩ := F.edge k hk hk0
    obtain ⟨t, ht, rfl⟩ := OrbTr.mem_steps hs
    exact ⟨h, hh, t, ht, e⟩
  · intro k hk hk0
    obtain ⟨e1, e2, e3⟩ := R.edge k hk hk0
    rw [hcnt] at e2
    obtain ⟨t, ht, et⟩ := OrbTr.mem_steps (rawStep_mem e2)
    refine ⟨_, e1, t, ht, ?_⟩
    rw [et, ← hstep _ e2 _ (R.pt _ (by omega)).1]
    exact e3
  · intro h hh t ht
    exact F.closed h hh _ (by rw [getElem!_pos st t ht]; exact Array.getElem_mem ht)
  · intro h hh t ht
    have hm : st[t]! ∈ rawSteps 2300 S3 thB j := by
      rw [mem_rawSteps_iff, getElem!_pos st t ht]
      exact Array.getElem_mem ht
    obtain ⟨l, hl, el⟩ := OrbTr.mem_steps hm
    have hpn := (R.pt h hh).1
    have hc := R.closed h hh l (by rw [hcnt]; exact hl)
    rw [hstep l hl _ hpn, el] at hc
    exact ⟨_, hc, R.pos _ (hst _ (by rw [← el]; exact rawStep_mem hl) _ hpn) hc⟩

theorem locU_ne_one :
    locU ≠ 1 := by
  intro e
  have h1 : uArr[thB[12]!]! = thB[12]! := by
    rw [rep_u.apply (thB_lt' (by norm_num : 12 < 13)), e]
    rfl
  rw [u_get (thB_lt' (by norm_num)), base_get (by norm_num)] at h1
  have h2 := move_ok
  rw [h1, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

theorem tr_ok
    {j : ℕ} (hj : j < 13) :
    (eqA 2300 thL[j]!.tr[0]! (idA 2300) &&
      allLt thL[j]!.tr.size (fun k => isInvA 2300 thL[j]!.tr[k]! (invCand 2300 thL[j]!.tr[k]!) &&
        fixesFirst thB thL[j]!.tr[k]! j &&
        siftA 2300 (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr 0 thL[j]!.tr[k]! &&
        allLt k (fun k' => (thL[j]!.tr[k]!)[thB[j]!]! != (thL[j]!.tr[k']!)[thB[j]!]!))) = true := by
  have F := lvFacts hj
  rw [Bool.and_eq_true]
  refine ⟨by rw [F.tr_zero]; exact CFSG.KS.Raw.eqA_self _, allLt_iff.2 fun k hk => ?_⟩
  rw [F.tr_size] at hk
  obtain ⟨⟨g, hgG, hg⟩, hb⟩ := F.tr_rep k hk
  have hgP : g ∈ stabB j := Gj_le hj.le hgG
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨isInvA_of_rep hg (rep_invCand hg), allLt_iff.2 fun t ht => ?_⟩, ?_⟩,
    allLt_iff.2 fun k' hk' => ?_⟩
  · have e := congrArg Fin.val (hgP.2 t ht)
    rw [← hg (bpt t), bpt_val' (by omega)] at e
    simpa using e
  · refine (siftA_iff_mem_originalSubgroup co2Q_chainArrays (by norm_num) co2Chain_check.1
      hg).2 ?_
    rw [co2Q_originalSubgroup]
    exact hgP.1
  · rw [hb, (F.tr_rep k' (by omega)).2, bne_iff_ne, ne_eq]
    intro e
    have := F.inj k hk k' (by omega) e
    omega

theorem thirdFactsK :
    ThirdFactsH where
  base_size := by rw [thB_size']; rfl
  base_lt := allLt_iff.2 fun _ hj => decide_eq_true (thB_lt' hj)
  L_size := by rw [thL_size']; rfl
  sizes := by
    refine beq_iff_eq.2 (List.ext_getElem (by simp [thL_size']) fun i h1 h2 => ?_)
    have hi : i < 13 := by simpa [thL_size'] using h1
    simp only [List.getElem_map, Array.getElem_toList]
    rw [← getElem!_pos thL i (by rw [thL_size']; exact hi), (lvFacts hi).tr_size,
      size_eq_rcnt hi, Nat.eq_of_beq_eq_true (allN_spec sizes_ok i hi), t3Sizes,
      List.getD_eq_getElem _ _ (by simpa using hi)]
  tr := allLt_iff.2 fun _ hj => tr_ok hj
  u_inv := isInvA_of_rep rep_u (rep_invCand rep_u)
  u_fix := u_fixK

end CertificateChecks.KernelSporSch.Co2M
