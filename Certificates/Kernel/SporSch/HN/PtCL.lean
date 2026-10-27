
module

public import Certificates.Kernel.SporSch.HN.PtCR
public import CFSG.Certificates.Kernel.SporSch.HNXChunkSound
public import CFSG.Certificates.Kernel.Spor.PWord
public import CFSG.Sporadic.HNSchreier.ThreeCheckInputs
public import Certificates.Data.CFSGNative.ONSchreier.Tools
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelSporSch.HNPtC

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KS CFSG.KS.SporSch CFSG.KS.HNArr CFSG.KS.Ord
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier.Native
open CFSG.ONSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HNArrS
open CertificateChecks.KernelSporSch.HNPt2103 Matrix

local notation "OM" => ordMat 5 133 13 1729

theorem chunk_img {r : RH}
    {W TW : ℕ} (hW : Canon 5 133 13 W) (hm : OM W = matR r) (hT : trM W = TW) {N nc P : ℕ}
    {IL : ℕ → ℕ} (hN : N ≤ 64 * nc)
    (h : allN nc (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M TW (sliceP P m) (IL m) (cntP N m)) = true)
    {p : ℕ} (hp : p < N) (h1 : fldW P (21 * p) 21 < nPts)
    (h2 : fldW (IL (p / 64)) (21 * (p % 64)) 21 < nPts) :
    ((r • (⟨fldW P (21 * p) 21, h1⟩ : X) : X) : ℕ) = fldW (IL (p / 64)) (21 * (p % 64)) 21 := by
  obtain ⟨hm1, hk, hc, he⟩ := HNXP.chunk_pos hN hp
  have hck : ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M (trM W)
      (sliceP P (p / 64)) (IL (p / 64)) (cntP N (p / 64)) = true := by
    rw [hT]
    exact allN_spec h (p / 64) hm1
  have hf : fldW (sliceP P (p / 64)) (21 * (p % 64)) 21 = fldW P (21 * p) 21 := by
    rw [HNXP.fld_sliceP _ _ (by omega), he]
  have e : (⟨fldW P (21 * p) 21, h1⟩ : X) = ⟨fldW (sliceP P (p / 64)) (21 * (p % 64)) 21,
      by rw [hf]; exact h1⟩ := Fin.ext hf.symm
  rw [e]
  exact ri_pts hW hm hc hck hk _ h2

theorem chunk_perm {r : RH}
    {W TW : ℕ} (hW : Canon 5 133 13 W) (hm : OM W = matR r) (hT : trM W = TW) {N nc P S : ℕ}
    (hN : N ≤ 64 * nc)
    (h : allN nc (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M TW (sliceP P m) (imgP P S m (cntP N m)) (cntP N m)) = true)
    {p : ℕ} (hp : p < N) (h1 : fldW P (21 * p) 21 < nPts)
    (h2 : fldW P (21 * fldW S (14 * p) 14) 21 < nPts) :
    ((r • (⟨fldW P (21 * p) 21, h1⟩ : X) : X) : ℕ) = fldW P (21 * fldW S (14 * p) 14) 21 := by
  obtain ⟨-, hk, hc, he⟩ := HNXP.chunk_pos hN hp
  have hf : fldW (imgP P S (p / 64) (cntP N (p / 64))) (21 * (p % 64)) 21 =
      fldW P (21 * fldW S (14 * p) 14) 21 := by
    rw [(HNXP.fld_imgP P S (p / 64) _).2 _ hk, he]
  rw [← hf]
  exact chunk_img (IL := fun m => imgP P S m (cntP N m)) hW hm hT hN h hp h1 (by rw [hf]; exact h2)

theorem chunk_list {r : RH}
    {W TW : ℕ} (hW : Canon 5 133 13 W) (hm : OM W = matR r) (hT : trM W = TW) {N nc P Q : ℕ}
    (hN : N ≤ 64 * nc)
    (h : allN nc (fun m => ptsImg CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.MS CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M TW (sliceP P m) (sliceP Q m) (cntP N m)) = true)
    {p : ℕ} (hp : p < N) (h1 : fldW P (21 * p) 21 < nPts) (h2 : fldW Q (21 * p) 21 < nPts) :
    ((r • (⟨fldW P (21 * p) 21, h1⟩ : X) : X) : ℕ) = fldW Q (21 * p) 21 := by
  obtain ⟨-, -, -, he⟩ := HNXP.chunk_pos hN hp
  have hf : fldW (sliceP Q (p / 64)) (21 * (p % 64)) 21 = fldW Q (21 * p) 21 := by
    rw [HNXP.fld_sliceP _ _ (by omega), he]
  rw [← hf]
  exact chunk_img (IL := fun m => sliceP Q m) hW hm hT hN h hp h1 (by rw [hf]; exact h2)

theorem countP_range (n : ℕ) (p : ℕ → Bool) :
    (List.range n).countP p = ((Finset.range n).filter fun x => p x = true).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n = true
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp), List.countP_singleton, if_pos hp]
    · rw [if_neg hp, List.countP_singleton, if_neg hp, Nat.add_zero]

theorem subI_mat {W : ℕ} (hW : Canon 5 133 13 W) :
    Canon 5 133 13 (CFSG.KC.LL.HN.subI W) ∧ OM (CFSG.KC.LL.HN.subI W) = OM W - 1 := by
  have e : CFSG.KC.LL.HN.subI W = CFSG.KC.Ord.redP 13 CFSG.KD.OrdHN.L
      CFSG.KD.OrdHN.H 5 9 (W + 4 * CFSG.KD.OrdHN.ONE) := by
    unfold CFSG.KC.LL.HN.subI
    congr 1
  rw [e]
  exact CFSG.KS.HNLocal.subOne_sound CFSG.KD.OrdHN.consts hW

theorem countP_fix {t : Array ℕ}
    {r : RH} (ht : PRep hnsData.n t (permR r)) {W G v : ℕ} (hW : Canon 5 133 13 W)
    (hm : OM W = matR r) (hG : trM (CFSG.KC.LL.HN.subI W) = G)
    (hs : ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M [G] b (hnxC b) = v) :
    (List.range nPts).countP (fun x => t[x]! == x) = v := by
  obtain ⟨hs1, hs2⟩ := subI_mat hW
  have h := HNXP.card_fix_eq (T := CFSG.KD.LgHNX.TX) consts_parts.1 hs1
  rw [hG, hs] at h
  rw [countP_range, ← h]
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  have hi' : i < nPts := Finset.mem_range.1 hi
  rw [hs2, ← PK_eq hi', Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero, hm, beq_iff_eq,
    ht.apply hi', permR_apply]
  have e : vL ((r • (⟨i, hi'⟩ : X) : X) : ℕ) = matR r *ᵥ PK i := by
    rw [vL_smul]
    change matR r *ᵥ vL i = _
    rw [vL_eq hi']
  constructor
  · intro h1
    rw [← e, h1]
    exact vL_eq hi'
  · intro h1
    have e2 : vL ((r • (⟨i, hi'⟩ : X) : X) : ℕ) = vL ((⟨i, hi'⟩ : X) : ℕ) := by
      rw [e, h1]
      exact (vL_eq hi').symm
    exact congrArg Fin.val (vL_injective e2)

theorem fixSum_of {G lo n v lo' n' v' : ℕ} (h : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3
    CFSG.KD.LgHNX.M G lo n) v = true) (h1 : lo = lo') (h2 : n = n') (h3 : v = v') :
    fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G lo' n' = v' := by
  subst h1 h2 h3
  exact Nat.eq_of_beq_eq_true h

theorem total8 {G v0 v1 v2 v3 v4 v5 v6 v7 : ℕ}
    (h0 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 0 2227 = v0)
    (h1 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 2227 2227 = v1)
    (h2 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 4454 2227 = v2)
    (h3 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 6681 2227 = v3)
    (h4 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 8908 2227 = v4)
    (h5 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 11135 2227 = v5)
    (h6 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 13362 2227 = v6)
    (h7 : fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G 15589 2224 = v7) :
    ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [G] b
      (hnxC b) = v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 := by
  have z : ∑ b ∈ Finset.range 0, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3
      CFSG.KD.LgHNX.M [G] b (hnxC b) = 0 := rfl
  have s0 := HNXP.fixSum_add _ _ _ _ h0 z
  have s1 := HNXP.fixSum_add _ _ _ _ h1 s0
  have s2 := HNXP.fixSum_add _ _ _ _ h2 s1
  have s3 := HNXP.fixSum_add _ _ _ _ h3 s2
  have s4 := HNXP.fixSum_add _ _ _ _ h4 s3
  have s5 := HNXP.fixSum_add _ _ _ _ h5 s4
  have s6 := HNXP.fixSum_add _ _ _ _ h6 s5
  have s7 := HNXP.fixSum_add _ _ _ _ h7 s6
  rw [Nat.zero_add] at s7
  exact s7

theorem total8' {G a0 a1 a2 a3 a4 a5 a6 a7 n0 n1 n2 n3 n4 n5 n6 n7 v0 v1 v2 v3 v4 v5 v6 v7 : ℕ}
    (h0 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a0 n0) v0 = true)
    (h1 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a1 n1) v1 = true)
    (h2 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a2 n2) v2 = true)
    (h3 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a3 n3) v3 = true)
    (h4 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a4 n4) v4 = true)
    (h5 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a5 n5) v5 = true)
    (h6 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a6 n6) v6 = true)
    (h7 : Nat.beq (fixSum CFSG.KD.LgHNX.TX CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M G a7 n7) v7 = true)
    (hb : a0 = 0 ∧ a1 = 2227 ∧ a2 = 4454 ∧ a3 = 6681 ∧ a4 = 8908 ∧ a5 = 11135 ∧ a6 = 13362 ∧
      a7 = 15589 ∧ n0 = 2227 ∧ n1 = 2227 ∧ n2 = 2227 ∧ n3 = 2227 ∧ n4 = 2227 ∧ n5 = 2227 ∧
      n6 = 2227 ∧ n7 = 2224 := by decide) :
    ∑ b ∈ Finset.range 17813, fixLeaf CFSG.KD.LgHNX.TX 464 CFSG.KD.LgHNX.CM3 CFSG.KD.LgHNX.M [G] b
      (hnxC b) = v0 + v1 + v2 + v3 + v4 + v5 + v6 + v7 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, c0, c1, c2, c3, c4, c5, c6, c7⟩ := hb
  exact total8 (fixSum_of h0 b0 c0 rfl) (fixSum_of h1 b1 c1 rfl) (fixSum_of h2 b2 c2 rfl)
    (fixSum_of h3 b3 c3 rfl) (fixSum_of h4 b4 c4 rfl) (fixSum_of h5 b5 c5 rfl)
    (fixSum_of h6 b6 c6 rfl) (fixSum_of h7 b7 c7 rfl)

theorem fix_listed {t : Array ℕ} {N : ℕ} {L : ℕ → ℕ}
    (hc : (List.range nPts).countP (fun x => t[x]! == x) = N)
    (hL : ∀ k < N, L k < nPts ∧ t[L k]! = L k) (hinj : ∀ k < N, ∀ k' < N, L k = L k' → k = k')
    {i : ℕ} (hi : i < nPts) (hf : t[i]! = i) : ∃ k < N, L k = i := by
  rw [countP_range] at hc
  have hsub : (Finset.range N).image L ⊆ (Finset.range nPts).filter fun x => (t[x]! == x) = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
    have hk' := Finset.mem_range.1 hk
    rw [Finset.mem_filter, Finset.mem_range, beq_iff_eq]
    exact hL k hk'
  have hcard : ((Finset.range N).image L).card = N := by
    rw [Finset.card_image_of_injOn fun a ha b hb e => hinj a (Finset.mem_coe.1 ha |>
      Finset.mem_range.1) b (Finset.mem_coe.1 hb |> Finset.mem_range.1) e, Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hc, hcard])
  have hm : i ∈ (Finset.range N).image L := by
    rw [heq, Finset.mem_filter, Finset.mem_range, beq_iff_eq]
    exact ⟨hi, hf⟩
  obtain ⟨k, hk, e⟩ := Finset.mem_image.1 hm
  exact ⟨k, Finset.mem_range.1 hk, e⟩

theorem incr_lt {N : ℕ} {L : ℕ → ℕ} (h : ∀ k, k + 1 < N → L k < L (k + 1)) :
    ∀ i j, i < j → j < N → L i < L j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | rfl
    · exact lt_trans (ih h1 (by omega)) (h j hj)
    · exact h i hj

theorem sorted_pairwise : ∀ {L : List ℕ}, (L.zip L.tail).all (fun p => decide (p.1 < p.2)) = true →
    L.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: rest, h => by
    have h' : decide (a < b) = true ∧ ((b :: rest).zip rest).all
        (fun p => decide (p.1 < p.2)) = true := by
      simpa [List.zip_cons_cons, List.all_cons] using h
    have hab : a < b := of_decide_eq_true h'.1
    have ih := sorted_pairwise (L := b :: rest) h'.2
    refine List.pairwise_cons.2 ⟨fun c hc => ?_, ih⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact lt_trans hab (List.rel_of_pairwise_cons ih hc)

theorem sorted_lt {F : Array ℕ} (h : (F.toList.zip F.toList.tail).all (fun p => decide (p.1 < p.2)) =
    true) {i j : ℕ} (hij : i < j) (hj : j < F.size) : F[i]! < F[j]! := by
  have hp := List.pairwise_iff_getElem.1 (sorted_pairwise h) i j (by simp; omega) (by simpa using hj)
    hij
  rw [HNXP.arr_get_toList, HNXP.arr_get_toList, getElem!_pos F.toList i (by simp; omega),
    getElem!_pos F.toList j (by simpa using hj)]
  exact hp

theorem posArr_of {F : Array ℕ} (hF : ∀ i < F.size, F[i]! < nPts)
    (h : (F.toList.zip F.toList.tail).all (fun p => decide (p.1 < p.2)) = true) :
    (posArr nPts F).size = nPts ∧ ∀ i < F.size, (posArr nPts F)[F[i]!]! = i :=
  PW.posArr_spec hF fun i hi j hj => (Nat.ne_of_lt (sorted_lt h hj hi))

theorem fixListOK_of {t : Array ℕ} {L : List ℕ}
    (hs : (L.zip L.tail).all (fun p => decide (p.1 < p.2)) = true)
    (hl : ∀ x ∈ L, x < nPts ∧ t[x]! = x)
    (hc : (List.range nPts).countP (fun x => t[x]! == x) = L.length) :
    fixListOK nPts t L = true := by
  unfold fixListOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hs, List.all_eq_true.2 fun x hx => ?_⟩, hc⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact hl x hx

theorem pointsOK_of {F : Array ℕ} (hF : ∀ i < F.size, F[i]! < nPts)
    (h : (F.toList.zip F.toList.tail).all (fun p => decide (p.1 < p.2)) = true) :
    pointsOK nPts F (posArr nPts F) = true := by
  obtain ⟨h1, h2⟩ := posArr_of hF h
  unfold pointsOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨h1, allBelowN_iff.2 fun k hk => ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨hF k hk, h2 k hk⟩

theorem restrictOK_of {T F s : Array ℕ} (hF : ∀ i < F.size, F[i]! < nPts)
    (h : (F.toList.zip F.toList.tail).all (fun p => decide (p.1 < p.2)) = true)
    (himg : ∀ k < F.size, s[k]! < F.size ∧ T[F[k]!]! = F[s[k]!]!) :
    restrictOK T F (posArr nPts F) s = true := by
  obtain ⟨-, h2⟩ := posArr_of hF h
  unfold restrictOK peq
  refine allBelowN_iff.2 fun k hk => ?_
  unfold restrictTab
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map, ← getElem!_pos F k hk,
    (himg k hk).2, h2 _ (himg k hk).1]
  exact beq_self_eq_true _

end CertificateChecks.KernelSporSch.HNPtC

end
