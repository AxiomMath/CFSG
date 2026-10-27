
module

public import Certificates.Kernel.Sporadic.OddCore.SuzWF
public import Certificates.Kernel.Sporadic.L2.XC

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ElimCert CFSG.Sporadic.SuzRecog
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pc" => pcomp 1782 11 (mask 11)

attribute [local irreducible] hexTable LevelTwoPins.nbPHex LevelTwoPins.nbQHex LevelTwoPins.triHex
  LevelTwoPins.triIdxHex LevelTwoPins.eltHex

theorem hE : ∀ k < 21, eltOK k = true :=
  slices (len := 7) (k := 3) (by norm_num) (by norm_num) eltAll

theorem eltPin_fst {k : Nat} (hk : k < 21) : (eltPin k).1 = unpack 1782 11 (L2EL.F k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable_sound L2EL.all k hk
  rw [← L2EL.eq] at h
  exact h

theorem eltP {k : Nat} (hk : k < 21) :
    P (eltPin k).1 (L2EL.F k) ∧ P (eltPin k).2 (L2EI k) ∧
      elemOK (eltPin k).1 (eltPin k).2 = true := by
  have h := hE k hk
  unfold eltOK elemK at h
  rw [band, band, band] at h
  obtain ⟨hc, hci, hinv, hm⟩ := h
  have e1 := eltPin_fst hk
  have hs := invEqK_sound hinv
  have e2 : (eltPin k).2 = unpack 1782 11 (L2EI k) := by
    change invCand 1782 (eltPin k).1 = _
    rw [e1]
    exact hs.1
  refine ⟨⟨e1, hc⟩, ⟨e2, hci⟩, ?_⟩
  unfold elemOK
  rw [e1, e2, hs.2, L2XCG.memX_of rfl hc hm]
  rfl

theorem sendsE_B {k : Nat} (hk : k < 21) {v v' : Nat} (hv : v < 2997)
    (h : sendsE k v v' = true) : sendsB (eltPin k).1 (eltPin k).2 v v' = true := by
  rw [sendsB_eq (hvA vtxOK) (hvW vtxOK) (eltP hk).1 (eltP hk).2.1 hv]
  exact h

theorem genP_get {l : Nat} (hl : l < 6) : genP[l]! = eltPin l := by
  unfold genP
  rw [getElem!_pos _ l (by rw [Array.size_ofFn]; exact hl), Array.getElem_ofFn]

theorem genQ_get {l : Nat} (hl : l < 6) : genQ[l]! = eltPin (6 + l) := by
  unfold genQ
  rw [getElem!_pos _ l (by rw [Array.size_ofFn]; exact hl), Array.getElem_ofFn]

theorem not_or_of {a b : Bool} (h : bIf(a, b, true) = true) : (!a || b) = true := by
  cases a <;> simp_all

theorem bdec {p : Prop} [Decidable p] (h : p) : decide p = true := decide_eq_true h

theorem npK_get {r k : Nat} (hr : r < 3) (hk : k < 36) :
    (hexTable 3 36 (36 * r) LevelTwoPins.nbPHex)[k]! = npK r k := by
  rw [hexTable_at hk]
  exact hexE L2NP.eq L2NP.all hr hk

theorem nqK_get {r m : Nat} (hr : r < 4) (hm : m < 315) :
    (hexTable 3 315 (315 * r) LevelTwoPins.nbQHex)[m]! = nqK r m := by
  rw [hexTable_at hm]
  exact hexE L2NQ.eq L2NQ.all hr hm

theorem trK_get {r t : Nat} (hr : r < 4) (ht : t < 180) :
    (hexTable 3 180 (180 * r) LevelTwoPins.triHex)[t]! = trK r t := by
  rw [hexTable_at ht]
  exact hexE L2TR.eq L2TR.all hr ht

theorem tiK_get {e : Nat} (he : e < 324) : triIdx[e]! = tiK e := by
  unfold triIdx
  rw [hexTable_at he, show 0 + e = 324 * 0 + e by omega]
  exact hexE L2TI.eq L2TI.all (by norm_num) he

theorem nbPPar_get {k : Nat} (hk : k < 36) : nbPPar[k]! = npK 0 k := by
  unfold nbPPar
  exact npK_get (r := 0) (by norm_num) hk
theorem nbPLab_get {k : Nat} (hk : k < 36) : nbPLab[k]! = npK 1 k := by
  unfold nbPLab
  exact npK_get (r := 1) (by norm_num) hk
theorem nbPDep_get {k : Nat} (hk : k < 36) : nbPDep[k]! = npK 2 k := by
  unfold nbPDep
  exact npK_get (r := 2) (by norm_num) hk
theorem nbQ_get {m : Nat} (hm : m < 315) : nbQ[m]! = nqK 0 m := by
  unfold nbQ
  exact nqK_get (r := 0) (by norm_num) hm
theorem nbQPar_get {m : Nat} (hm : m < 315) : nbQPar[m]! = nqK 1 m := by
  unfold nbQPar
  exact nqK_get (r := 1) (by norm_num) hm
theorem nbQLab_get {m : Nat} (hm : m < 315) : nbQLab[m]! = nqK 2 m := by
  unfold nbQLab
  exact nqK_get (r := 2) (by norm_num) hm
theorem nbQDep_get {m : Nat} (hm : m < 315) : nbQDep[m]! = nqK 3 m := by
  unfold nbQDep
  exact nqK_get (r := 3) (by norm_num) hm
theorem triY1_get {t : Nat} (ht : t < 180) : triY1[t]! = trK 0 t := by
  unfold triY1
  exact trK_get (r := 0) (by norm_num) ht
theorem triY2_get {t : Nat} (ht : t < 180) : triY2[t]! = trK 1 t := by
  unfold triY2
  exact trK_get (r := 1) (by norm_num) ht
theorem triPar_get {t : Nat} (ht : t < 180) : triPar[t]! = trK 2 t := by
  unfold triPar
  exact trK_get (r := 2) (by norm_num) ht
theorem triLab_get {t : Nat} (ht : t < 180) : triLab[t]! = trK 3 t := by
  unfold triLab
  exact trK_get (r := 3) (by norm_num) ht

theorem nbQ_size : nbQ.size = 315 := by unfold nbQ hexTable; rw [Array.size_ofFn]

theorem n0_get {k : Nat} (hk : k < 36) : (nbr[0]!)[k]! = nbK 0 k := nbr_get (by norm_num) hk

theorem p1_eq : p1 = 342 := SuzWF.p1_eq

theorem nbK_lt {x k : Nat} (hx : x < 2835) (hk : k < 36) : nbK x k < 2997 := by
  have h := hgr x (by omega)
  unfold grChk grK at h
  rw [band, show Nat.blt x 2835 = true from nblt.2 hx] at h
  exact nblt.1 ((band _ _).1 (allN_get h.1 hk)).1

theorem nbPOK_true : nbPOK = true := by
  have k0 := kNbP
  unfold nbPK at k0
  rw [band, band, band] at k0
  obtain ⟨k1, k2, k3, k4⟩ := k0
  have N1 : (allLt 6 fun l => elemOK genP[l]!.1 genP[l]!.2 && sendsB genP[l]!.1 genP[l]!.2 0 0) =
      true := allLt_iff.2 fun l hl => by
    rw [genP_get hl]
    exact Bool.and_eq_true_iff.2 ⟨(eltP (by omega)).2.2,
      sendsE_B (by omega) (by norm_num) (allN_get k1 hl)⟩
  have N5 : (allLt 2997 fun y => !adjB nbr 0 y || occB nbr[0]! y) = true := allLt_iff.2 fun y hy => by
    rw [adjB_eq, occB_eq]
    exact not_or_of (allN_get k4 hy)
  have N6 : (allLt 36 fun k => (decide (k < 18) == decide ((nbr[0]!)[k]! < 2835)) &&
      (k == 0 || k == 18 || (decide (nbPPar[k]! < 36) && decide (nbPDep[nbPPar[k]!]! < nbPDep[k]!) &&
        decide (nbPLab[k]! < 6) &&
        sendsB genP[nbPLab[k]!]!.1 genP[nbPLab[k]!]!.2 (nbr[0]!)[nbPPar[k]!]! (nbr[0]!)[k]!))) =
      true := allLt_iff.2 fun k hk => by
    have h := slices (len := 18) (k := 2) (by norm_num) (by norm_num) nbPAll k hk
    unfold nbPStep at h
    rw [band, nbeq] at h
    obtain ⟨ht, hr⟩ := h
    rw [n0_get hk]
    refine Bool.and_eq_true_iff.2 ⟨?_, ?_⟩
    · have hiff : k < 18 ↔ nbK 0 k < 2835 := by
        rw [Q3AG.nIf_eq, Q3AG.nIf_eq] at ht
        by_cases h1 : k < 18 <;> by_cases h2 : nbK 0 k < 2835
        · exact iff_of_true h1 h2
        · simp [show Nat.blt k 18 = true from nblt.2 h1, nblt_f h2] at ht
        · simp [nblt_f h1, show Nat.blt (nbK 0 k) 2835 = true from nblt.2 h2] at ht
        · exact iff_of_false h1 h2
      rw [beq_iff_eq, decide_eq_decide]
      exact hiff
    · by_cases h0 : k = 0
      · simp [h0]
      by_cases h18 : k = 18
      · simp [h18]
      rw [Q3AG.nbeq_false h0, Q3AG.nbeq_false h18, sB, sB] at hr
      change bAnd(Nat.blt (npK 0 k) 36, bAnd(Nat.blt (npK 2 (npK 0 k)) (npK 2 k),
        bAnd(Nat.blt (npK 1 k) 6, sendsE (npK 1 k) (nbK 0 (npK 0 k)) (nbK 0 k)))) = true at hr
      rw [band, band, band, nblt, nblt, nblt] at hr
      obtain ⟨ha, hd, hl, hs⟩ := hr
      rw [nbPPar_get hk, nbPLab_get hk, nbPDep_get hk, nbPDep_get ha, genP_get hl, n0_get ha]
      simp only [Bool.or_eq_true, beq_iff_eq, h0, h18, false_or, Bool.and_eq_true,
        decide_eq_true_eq]
      exact ⟨⟨⟨ha, hd⟩, hl⟩, sendsE_B (by omega) (nbK_lt (by norm_num) ha) hs⟩
  unfold nbPOK
  simp only [N1, N5, N6, Bool.and_true, Bool.true_and, beq_iff_eq, Bool.and_eq_true]
  exact ⟨⟨nbr_size (by norm_num), by rw [n0_get (by norm_num), p1_eq]; exact nbeq.1 k2⟩,
    by rw [n0_get (by norm_num)]; exact nbeq.1 k3⟩

theorem sendsK_lt {G GI v v' : Nat} (h : sendsK G GI v v' = true) : v' < 2997 := by
  unfold sendsK at h
  rw [bif_true] at h
  by_cases hv : v < 2835
  · have := h.1 (nblt.2 hv)
    rw [band, nblt] at this
    omega
  · have := h.2 (nblt_f hv)
    rw [band, band, nble, nblt] at this
    exact this.2.1

theorem nbQ0 : nqK 0 0 = 0 := by
  have k0 := kNbQ
  unfold nbQK at k0
  rw [band, band] at k0
  exact nbeq.1 k0.2.1

theorem nbQ_lt : ∀ d, ∀ m < 315, nqK 3 m = d → nqK 0 m < 2997 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro m hm hd
    have h := slices (len := 20) (k := 16) (by norm_num) (by norm_num) nbQAll m hm
    unfold nbQStep at h
    by_cases h0 : m = 0
    · subst h0
      rw [nbQ0]
      norm_num
    · rw [Q3AG.nbeq_false h0, show Nat.blt m 315 = true from nblt.2 hm, sB, sB] at h
      change bAnd(Nat.blt (nqK 1 m) 315, bAnd(Nat.blt (nqK 3 (nqK 1 m)) (nqK 3 m),
        bAnd(Nat.blt (nqK 2 m) 6, sendsE (Nat.add 6 (nqK 2 m)) (nqK 0 (nqK 1 m)) (nqK 0 m)))) =
        true at h
      rw [band, band, band] at h
      exact sendsK_lt h.2.2.2

theorem nbQOK_true : nbQOK = true := by
  have k0 := kNbQ
  unfold nbQK at k0
  rw [band, band] at k0
  obtain ⟨k1, k2, k3⟩ := k0
  have N1 : (allLt 6 fun l => elemOK genQ[l]!.1 genQ[l]!.2 &&
      sendsB genQ[l]!.1 genQ[l]!.2 2835 2835) = true := allLt_iff.2 fun l hl => by
    rw [genQ_get hl]
    exact Bool.and_eq_true_iff.2 ⟨(eltP (by omega)).2.2,
      sendsE_B (by omega) (by norm_num) (allN_get k1 hl)⟩
  have N3 : (allLt 2997 fun y => !adjB nbr 2835 y || occB nbQ y) = true := allLt_iff.2 fun y hy => by
    rw [adjB_eq]
    have h := allN_get k3 hy
    cases ha : adjK 2835 y
    · rfl
    · rw [ha] at h
      change occQ y = true at h
      unfold occQ at h
      simp only [Bool.not_true, Bool.false_or]
      unfold occB
      rw [nbQ_size, List.any_eq_true]
      by_contra hno
      rw [Bool.not_eq_true', Bool.eq_false_iff] at h
      apply h
      refine CFSG.KS.Raw.allN_of_forall fun m hm => ?_
      cases hb : Nat.beq (nqK 0 m) y
      · rfl
      · exact absurd ⟨m, List.mem_range.2 hm, by rw [nbQ_get hm, Q3AG.beqN, hb]⟩ hno
  have N4 : (allLt 315 fun m => m == 0 || (decide (nbQPar[m]! < 315) &&
      decide (nbQDep[nbQPar[m]!]! < nbQDep[m]!) && decide (nbQLab[m]! < 6) &&
      sendsB genQ[nbQLab[m]!]!.1 genQ[nbQLab[m]!]!.2 nbQ[nbQPar[m]!]! nbQ[m]!)) = true :=
    allLt_iff.2 fun m hm => by
      by_cases h0 : m = 0
      · simp [h0]
      have h := slices (len := 20) (k := 16) (by norm_num) (by norm_num) nbQAll m hm
      unfold nbQStep at h
      rw [Q3AG.nbeq_false h0, show Nat.blt m 315 = true from nblt.2 hm, sB, sB] at h
      change bAnd(Nat.blt (nqK 1 m) 315, bAnd(Nat.blt (nqK 3 (nqK 1 m)) (nqK 3 m),
        bAnd(Nat.blt (nqK 2 m) 6, sendsE (Nat.add 6 (nqK 2 m)) (nqK 0 (nqK 1 m)) (nqK 0 m)))) =
        true at h
      rw [band, band, band, nblt, nblt, nblt] at h
      obtain ⟨ha, hd, hl, hs⟩ := h
      rw [nbQPar_get hm, nbQLab_get hm, nbQDep_get hm, nbQDep_get ha, genQ_get hl, nbQ_get ha,
        nbQ_get hm]
      simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨ha, hd⟩, hl⟩, sendsE_B (by omega) (nbQ_lt _ _ ha rfl) hs⟩
  unfold nbQOK
  simp only [N1, N3, N4, Bool.and_true, Bool.true_and, beq_iff_eq]
  rw [nbQ_get (by norm_num)]
  exact nbeq.1 k2

theorem actV_W {g gi : Array Nat} {G GI : Nat} (hg : P g G) (hgi : P gi GI) {j v' : Nat}
    (hj : j < 162) (h : sendsK G GI (2835 + j) v' = true) : actV g gi (2835 + j) = v' := by
  have hw := hvW vtxOK
  unfold sendsK at h
  rw [nblt_f (show ¬ 2835 + j < 2835 by omega), show Nat.sub (2835 + j) 2835 = j from
    Nat.add_sub_cancel_left 2835 j] at h
  change bAnd(Nat.ble 2835 v', bAnd(Nat.blt v' 2997, strictB (pc G (pc (TK j 0) GI)) fun C =>
    strictB (Nat.sub v' 2835) fun j' =>
      bIf(Nat.beq (TK j' 0) C, true, bIf(Nat.beq (TK j' 1) C, true, Nat.beq (TK j' 2) C)))) =
    true at h
  rw [band, band, nble, nblt, sB, sB] at h
  obtain ⟨h1, h2, h3⟩ := h
  set C := pc G (pc (TK j 0) GI)
  have hC : P (conjA g gi wPts[j]!) C := p_conj hg hgi (pW hw hj)
  have hj' : v' - 2835 < 162 := by omega
  have key : ∃ k < 3, fp (conjA g gi wPts[j]!) = fT (3 * (v' - 2835) + k) := by
    simp only [bif_true, nbeq] at h3
    by_cases e0 : TK (v' - 2835) 0 = C
    · exact ⟨0, by norm_num, by rw [hC.1, fp_unpack, ← e0]; rfl⟩
    · have h3' := h3.2 (Q3AG.nbeq_false e0)
      by_cases e1 : TK (v' - 2835) 1 = C
      · exact ⟨1, by norm_num, by rw [hC.1, fp_unpack, ← e1]; rfl⟩
      · exact ⟨2, by norm_num, by rw [hC.1, fp_unpack, ← h3'.2 (Q3AG.nbeq_false e1)]; rfl⟩
  obtain ⟨k, hk, hfk⟩ := key
  unfold actV
  rw [if_neg (by omega), show 2835 + j - 2835 = j by omega, fpConj_eq, hfk,
    vIdx_get hw kSortT hj' hk]
  omega

theorem cellReps_get {k : Nat} (hk : k < 4) : cellReps[k]! = crK k := by
  interval_cases k <;> rfl

theorem locOK_true : locOK = true := by
  have l0 := kLoc
  unfold locK at l0
  rw [band, band, band] at l0
  obtain ⟨l1, l2, l3, l4⟩ := l0
  have C : (allLt 4 fun k =>
      pElemOK (cellC k) 2835 cellReps[k]! && pElemOK (cellC' k) 2835 (actV (cellC' k).1 (cellC' k).2 2835) &&
        sendsB swapE.1 swapE.2 (actV (cellC' k).1 (cellC' k).2 2835) cellReps[k]!) = true :=
    allLt_iff.2 fun k hk => by
      have h := cellAll k hk
      unfold cellK at h
      rw [band, band, band, band] at h
      obtain ⟨c1, c2, c3, c4, c5⟩ := h
      have e1 : cellC k = eltPin (13 + k) := rfl
      have e2 : cellC' k = eltPin (17 + k) := rfl
      have hv : actV (cellC' k).1 (cellC' k).2 2835 = v1K k := by
        rw [e2]
        exact actV_W (eltP (by omega)).1 (eltP (by omega)).2.1 (j := 0) (by norm_num) c4
      have hv1 : v1K k < 2997 := by interval_cases k <;> decide
      rw [hv, cellReps_get hk, e1, e2]
      unfold pElemOK
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨⟨(eltP (by omega)).2.2, sendsE_B (by omega) (by norm_num) c1⟩,
        sendsE_B (by omega) (by norm_num) c2⟩, ⟨(eltP (by omega)).2.2,
        sendsE_B (by omega) (by norm_num) c3⟩, sendsE_B (by omega) (by norm_num) c4⟩,
        sendsE_B (by norm_num) hv1 c5⟩
  unfold locOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, nbPOK_true⟩, nbQOK_true⟩, (eltP (by norm_num)).2.2⟩, ?_⟩, ?_⟩, rfl⟩, C⟩
  · rw [adjB_eq, p1_eq]; exact l1
  · rw [adjB_eq]; exact l2
  · rw [p1_eq]; exact sendsE_B (by norm_num) (by norm_num) l3
  · rw [p1_eq]; exact sendsE_B (by norm_num) (by norm_num) l4

theorem crK_lt {k : Nat} (hk : k < 4) : crK k < 2997 := by interval_cases k <;> decide

theorem tri_lt : ∀ t < 180, trK 0 t < 2997 ∧ trK 1 t < 2997 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    have h := slices (len := 10) (k := 18) (by norm_num) (by norm_num) triAll t ht
    unfold triStep at h
    by_cases h4 : t < 4
    · have hr := allN_get kTriR h4
      rw [band, nbeq, nbeq] at hr
      rw [hr.1, hr.2]
      exact ⟨by norm_num, crK_lt h4⟩
    · rw [nblt_f h4, show Nat.blt t 180 = true from nblt.2 ht, sB, sB] at h
      change bAnd(Nat.blt (trK 2 t) t, bAnd(Nat.blt (trK 3 t) 6,
        bAnd(sendsE (trK 3 t) (trK 0 (trK 2 t)) (trK 0 t),
          sendsE (trK 3 t) (trK 1 (trK 2 t)) (trK 1 t)))) = true at h
      rw [band, band, band, nblt] at h
      exact ⟨sendsK_lt h.2.2.1, sendsK_lt h.2.2.2⟩

theorem triOK_true : triOK = true := by
  have R : (allLt 4 fun k => triY1[k]! == p1 && triY2[k]! == cellReps[k]!) = true :=
    allLt_iff.2 fun k hk => by
      have hr := allN_get kTriR hk
      rw [band, nbeq, nbeq] at hr
      rw [triY1_get (by omega), triY2_get (by omega), p1_eq, cellReps_get hk, hr.1, hr.2]
      simp
  have T : (allLt 180 fun t => decide (t < 4) || (decide (triPar[t]! < t) && decide (triLab[t]! < 6) &&
      sendsB genP[triLab[t]!]!.1 genP[triLab[t]!]!.2 triY1[triPar[t]!]! triY1[t]! &&
      sendsB genP[triLab[t]!]!.1 genP[triLab[t]!]!.2 triY2[triPar[t]!]! triY2[t]!)) = true :=
    allLt_iff.2 fun t ht => by
      by_cases h4 : t < 4
      · simp [h4]
      have h := slices (len := 10) (k := 18) (by norm_num) (by norm_num) triAll t ht
      unfold triStep at h
      rw [nblt_f h4, show Nat.blt t 180 = true from nblt.2 ht, sB, sB] at h
      change bAnd(Nat.blt (trK 2 t) t, bAnd(Nat.blt (trK 3 t) 6,
        bAnd(sendsE (trK 3 t) (trK 0 (trK 2 t)) (trK 0 t),
          sendsE (trK 3 t) (trK 1 (trK 2 t)) (trK 1 t)))) = true at h
      rw [band, band, band, nblt, nblt] at h
      obtain ⟨ha, hl, s1, s2⟩ := h
      have ha' : trK 2 t < 180 := by omega
      rw [triPar_get ht, triLab_get ht, genP_get hl, triY1_get ha', triY1_get ht, triY2_get ha',
        triY2_get ht]
      simp only [Bool.or_eq_true, decide_eq_true_eq, h4, false_or, Bool.and_eq_true]
      exact ⟨⟨⟨ha, hl⟩, sendsE_B (by omega) (tri_lt _ ha').1 s1⟩, sendsE_B (by omega) (tri_lt _ ha').2 s2⟩
  have L : (allLt 18 fun a => allLt 18 fun b => !adjB nbr (nbr[0]!)[a]! (nbr[0]!)[18 + b]! ||
      (decide (triIdx[18 * a + b]! < 180) && triY1[triIdx[18 * a + b]!]! == (nbr[0]!)[a]! &&
        triY2[triIdx[18 * a + b]!]! == (nbr[0]!)[18 + b]!)) = true :=
    allLt_iff.2 fun a ha => allLt_iff.2 fun b hb => by
      have h := allN_get (allN_get kTriL ha) hb
      rw [n0_get (by omega), n0_get (by omega), adjB_eq, tiK_get (by omega)]
      change bIf(adjK (nbK 0 a) (nbK 0 (18 + b)), strictB (tiK (18 * a + b)) fun t =>
        bAnd(Nat.blt t 180, bAnd(Nat.beq (trK 0 t) (nbK 0 a), Nat.beq (trK 1 t) (nbK 0 (18 + b)))),
        true) = true at h
      cases hadj : adjK (nbK 0 a) (nbK 0 (18 + b))
      · rfl
      · rw [hadj, sB] at h
        change bAnd(Nat.blt (tiK (18 * a + b)) 180, bAnd(Nat.beq (trK 0 (tiK (18 * a + b))) (nbK 0 a),
          Nat.beq (trK 1 (tiK (18 * a + b))) (nbK 0 (18 + b)))) = true at h
        rw [band, band, nblt, nbeq, nbeq] at h
        obtain ⟨h1, h2, h3⟩ := h
        rw [triY1_get h1, triY2_get h1, h2, h3]
        simp [h1]
  unfold triOK
  simp only [R, T, L, Bool.and_self]

end CertificateChecks.KernelSpor.L2G

end
