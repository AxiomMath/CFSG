module

public import Certificates.Kernel.HSPinned6101.Check
public import Certificates.Kernel.HSPinned6101.Stars
public import Certificates.Kernel.HSMult.TabK
public import CFSG.Certificates.Kernel.HSPinned.PairCheckSound

public section

namespace CertificateChecks.KernelHSPinned6101

open Certificates.Kernel.HSPinned6101 CFSG.KC.HSPinned6101 CFSG.KC.HSPinnedBfs
  CFSG.Sporadic.Recognition.HSPinned.Native Certificates.Kernel.HSIdent CFSG.KC.HSIdent
  CFSG.Sporadic.HS.Native

theorem stars_lt : ∀ i < 100, ∀ t ∈ stars[i]!, t < 1100 := by
  intro i hi t ht
  have h := (testBit_lmask _ t).2 ht
  rw [lmask_eq lm_ok hi] at h
  exact lt_of_testBit_g1100 h

theorem stars_inj : ∀ i < 100, ∀ j < 100, i = j ∨ ∃ x ∈ stars[i]!, x ∉ stars[j]! := by
  intro i hi j hj
  by_contra hc
  push Not at hc
  obtain ⟨hne, hsub⟩ := hc
  have hsi := starAt_spec (allR_zero stars_ok i hi)
  have hsj := starAt_spec (allR_zero stars_ok j hj)
  have heq : (stars[i]!).toFinset = (stars[j]!).toFinset :=
    Finset.eq_of_subset_of_card_le (fun x hx => List.mem_toFinset.2 (hsub x (List.mem_toFinset.1 hx)))
      (by rw [List.toFinset_card_of_nodup hsj.2.1, List.toFinset_card_of_nodup hsi.2.1, hsj.1,
        hsi.1])
  have hm : lmask stars[i]! = lmask stars[j]! := Nat.eq_of_testBit_eq fun t => by
    apply Bool.eq_iff_iff.2
    rw [testBit_lmask, testBit_lmask, ← List.mem_toFinset, heq, List.mem_toFinset]
  have := allR_zero (allR_zero inj_ok i hi) j hj
  unfold injAt at this
  rw [← lmask_eq lm_ok hi, ← lmask_eq lm_ok hj, hm] at this
  simp [Nat.beq_eq, hne] at this

theorem wit_check : ∀ k < 20, wit[k]!.1 < 100 ∧ wit[k]!.2 < 100 ∧
    ∀ x < 1100, (x ∈ stars[wit[k]!.1]! ∧ x ∈ stars[wit[k]!.2]!) ↔ x = hsData.basis[k]! := by
  intro k hk
  have h := allR_zero wit_ok k hk
  unfold witAt at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, -⟩, h4⟩ := h
  have h4' : g1100 LM (wit[k]!).1 &&& g1100 LM (wit[k]!).2 = 2 ^ hsData.basis[k]! :=
    Nat.eq_of_beq_eq_true h4
  refine ⟨h1, h2, fun x _ => ?_⟩
  rw [← testBit_lmask, ← testBit_lmask, lmask_eq lm_ok h1, lmask_eq lm_ok h2, ← Bool.and_eq_true,
    ← Nat.testBit_and, h4', Nat.testBit_two_pow, decide_eq_true_eq, eq_comm]

theorem adj_spec : ∀ x < 100, ∀ y < 100,
    adjB x y = true ↔ (x ≠ y ∧ ∃ t ∈ stars[x]!, t ∈ stars[y]!) := by
  intro x hx y hy
  rw [adjB_eq hx hy, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, ← any_contains_iff,
    List.any_eq_true]
  simp only [List.contains_iff_mem]

theorem adjB_zero_four : adjB 0 4 = true := by
  rw [adjB_eq_adjK lm_ok (by omega) (by omega)]
  exact adj_zero_four

theorem adjB_zero_one : adjB 0 1 = false := by
  rw [adjB_eq_adjK lm_ok (by omega) (by omega)]
  exact not_adj_zero_one

theorem star_iff {f : Nat → Nat} {S T : List Nat} (hS : S.Nodup) (hT : T.length ≤ S.length)
    (hlt : ∀ t ∈ S, t < 1100) (hinj : ∀ i < 1100, ∀ j < 1100, f i = f j → i = j)
    (hf : ∀ x ∈ S, f x ∈ T) {x : Nat} (hx : x < 1100) : x ∈ S ↔ f x ∈ T := by
  refine ⟨hf x, fun h => ?_⟩
  have hsub : S.toFinset.image f ⊆ T.toFinset := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
    exact List.mem_toFinset.2 (hf z (List.mem_toFinset.1 hz))
  have hcard : T.toFinset.card ≤ (S.toFinset.image f).card := by
    rw [Finset.card_image_of_injOn fun a ha b hb e => hinj a (hlt a (List.mem_toFinset.1 ha)) b
      (hlt b (List.mem_toFinset.1 hb)) e, List.toFinset_card_of_nodup hS]
    exact (List.toFinset_card_le T).trans hT
  have hmem : f x ∈ S.toFinset.image f := by
    rw [Finset.eq_of_subset_of_card_le hsub hcard]
    exact List.mem_toFinset.2 h
  obtain ⟨y, hy, e⟩ := Finset.mem_image.1 hmem
  rw [← hinj y (hlt y (List.mem_toFinset.1 hy)) x hx e]
  exact List.mem_toFinset.1 hy

open CFSG.KC.VecK CertificateChecks.KernelVec.HS CertificateChecks.KernelHSMult
  CFSG.Sporadic.Th.Native CFSG.KC.M1F2 in
theorem starsClosed_check :
    starsClosedOK (hsData.orbit ()).alpha (hsData.orbit ()).beta = true := by
  have horb : ∀ h < (hsData ()).n, orbAt (hsData ()).d (hsData ()).n NA NB Pt AT BT h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact orb_0
      | 1, _ => exact orb_1
      | 2, _ => exact orb_2
      | 3, _ => exact orb_3
      | 4, _ => exact orb_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hbfs : ∀ h < (hsData ()).n, bfsAt (hsData ()).n AT BT FO h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact bfs_0
      | 1, _ => exact bfs_1
      | 2, _ => exact bfs_2
      | 3, _ => exact bfs_3
      | 4, _ => exact bfs_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hsort : ∀ h < (hsData ()).n, sortAt (hsData ()).n Pt S IP SP h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact sort_0
      | 1, _ => exact sort_1
      | 2, _ => exact sort_2
      | 3, _ => exact sort_3
      | 4, _ => exact sort_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hn' : (hsData ()).n = 1100 := rfl
  have hP := vpts_of hn horb hsort
  obtain ⟨ha, hb⟩ := orbit_real (hsData ()) hA hB hseed hn hP0 horb hbfs hsort
  have hO := orbit_eq (hsData ()) hA hB hseed hn hP0 horb hbfs hsort
  have hn32 : (hsData ()).n < 2 ^ 32 := by rw [hn']; omega
  have hap : ∀ (f : Nat → Nat), (∀ i < (hsData ()).n, f i < (hsData ()).n) → ∀ i < 1100,
      ap ((List.range (hsData ()).n).map fun h => UInt32.ofNat (f h)).toArray i = f i := by
    intro f hf i hi
    rw [← hn'] at hi
    unfold ap
    rw [getElem!_pos _ i (by simpa using hi)]
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range, UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by have := hf i hi; omega)
  have hapA : ∀ x < 1100, ap ((hsData ()).orbit ()).alpha x = lk AT 32 x := fun x hx => by
    rw [hO]
    exact hap _ (fun j hj => (orbAt_iff.1 (horb j hj)).2.1) x hx
  have hapB : ∀ x < 1100, ap ((hsData ()).orbit ()).beta x = lk BT 32 x := fun x hx => by
    rw [hO]
    exact hap _ (fun j hj => (orbAt_iff.1 (horb j hj)).2.2.1) x hx
  have hinj : ∀ {T : Table} {N X : Nat}, Realizes (hsData ()).d (hsData ()).n (lk Pt 32) T N →
      (∀ v < 2 ^ (hsData ()).d, vmF (hsData ()).d X (vmF (hsData ()).d N v) = v) →
      ∀ i < 1100, ∀ j < 1100, ap T i = ap T j → i = j := by
    intro T N X hT hX i hi j hj e
    rw [← hn'] at hi hj
    apply hP.inj i hi j hj
    rw [← hX _ (hP.lt i hi), ← hX _ (hP.lt j hj), ← (hT.2 i hi).2, ← (hT.2 j hj).2, e]
  have hiA : ∀ i < 1100, ∀ j < 1100, lk AT 32 i = lk AT 32 j → i = j := fun i hi j hj e =>
    hinj ha (fun v hv => vmF_inv hAi hv) i hi j hj (by rw [hapA i hi, hapA j hj, e])
  have hiB : ∀ i < 1100, ∀ j < 1100, lk BT 32 i = lk BT 32 j → i = j := fun i hi j hj e =>
    hinj hb (fun v hv => vmF_inv hBi hv) i hi j hj (by rw [hapB i hi, hapB j hj, e])
  unfold starsClosedOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨rfl, rfl⟩, rfl⟩, allIn_iff'.2 fun i _ hi => ?_⟩
  have hs := starAt_spec (allR_zero stars_ok i hi)
  obtain ⟨hvA, hvB⟩ := vtx_eq vab_ok hi
  obtain ⟨hlA, hlB⟩ := vtx_lt i hi
  have hsA := starAt_spec (allR_zero stars_ok _ hlA)
  have hsB := starAt_spec (allR_zero stars_ok _ hlB)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hlA, hlB⟩, allIn_iff'.2 fun x _ hx => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hapA x hx, hapB x hx]
  refine ⟨star_iff hs.2.1 (by rw [hsA.1, hs.1]) (stars_lt i hi) hiA
      (fun y hy => hvA ▸ (hs.2.2 y hy).1) hx,
    star_iff hs.2.1 (by rw [hsB.1, hs.1]) (stars_lt i hi) hiB
      (fun y hy => hvB ▸ (hs.2.2 y hy).2) hx⟩

theorem pairsA_all : ∀ y < dA.n, pairAt dA VAB y = true := by
  rw [nA_eq]
  exact allR_zero pairsA

theorem pairsN_all : ∀ y < dN.n, pairAt dN VAB y = true := by
  rw [nN_eq]
  exact allR_cons (allR_cons (allR_cons (allR_zero pairsN0) pairsN1) pairsN2) pairsN3

theorem flagAdj_check : pairOrbOK vtxA vtxB (pairCode 0 4) covAdj = true :=
  pairOrbOK_of vab_ok headA pairsA_all (allR_cons (allR_zero posA0) posA1) (covAdj_eq lm_ok)
    fun x hx y hy => allR_zero (allR_zero coverA x hx) y hy

theorem flagNon_check : pairOrbOK vtxA vtxB (pairCode 0 1) covNon = true :=
  pairOrbOK_of vab_ok headN pairsN_all (allR_cons (allR_zero posN0) posN1) (covNon_eq lm_ok)
    fun x hx y hy => allR_zero (allR_zero coverN x hx) y hy

end CertificateChecks.KernelHSPinned6101

end
