module

public import Certificates.Kernel.Misc.Perm.J2EnumTwin
public import Certificates.Kernel.Misc.Perm.J2Rel
public import CFSG.Certificates.Kernel.Misc.EnumBfsMem
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2C3 (hw hx hz hI pX pZ pI cm X Z I p3 p3p all_of_chunks)
open CertificateChecks.KernelMisc.J2Fam (R rX rZ rV1 rV2 rCC rwg0 rwg1 iv hvw pVW htw pTW hu4
  pU4 okvw oktw vw_size tw_size)
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.EnumBfs (enumBfs_mem any_congr_of_mem allLt_congr_of_mem)

@[expose] noncomputable def SPL (k : ℕ) : List ℕ :=
  if k = 0 then S0P else if k = 1 then S1P else S2P

theorem hSL (k : ℕ) (hk : k < 3) : (cSL k).pts.size = 64 ∧
    (∀ i < 64, (cSL k).pts[i]! = unpack 315 9 (lget (SPL k) i)) ∧
    ∀ i < 64, permB 315 9 (lget (SPL k) i) = true := by
  interval_cases k
  · have b := certL_bound 64 4 S0P S0E S0R S0L
    exact ⟨b.1, b.2.1, ptPerm (N := 64) (all_of_chunks 64 1 ptS0S)⟩
  · have b := certL_bound 64 4 S1P S1E S1R S1L
    exact ⟨b.1, b.2.1, ptPerm (N := 64) (all_of_chunks 64 1 ptS1S)⟩
  · have b := certL_bound 64 4 S2P S2E S2R S2L
    exact ⟨b.1, b.2.1, ptPerm (N := 64) (all_of_chunks 64 1 ptS2S)⟩

theorem memCS (k : ℕ) (hk : k < 3) : ∀ x, x ∈ (cS k).pts ↔ x ∈ (cSL k).pts := by
  have h : enumOK 315 (gensS k) keyPts (cSL k) = true := by
    interval_cases k
    · exact enumS0
    · exact enumS1
    · exact enumS2
  unfold cS
  exact enumBfs_mem h (by rw [(hSL k hk).1]; norm_num)

theorem inS (k : ℕ) (hk : k < 3) {t : Array ℕ} {p : ℕ} (ht : R t p) :
    inCert (cS k) t = memK 64 (lget (SPL k)) p := by
  unfold inCert
  rw [any_congr_of_mem (memCS k hk), ht.1]
  exact any_eqA_unpack hw (hSL k hk).1 (hSL k hk).2.1 (hSL k hk).2.2 ht.2

theorem inP3 {t : Array ℕ} {p : ℕ} (ht : R t p) : inCert cP3 t = memK 27 J2C3.P3P.F p := by
  unfold inCert
  rw [ht.1]
  exact any_eqA_unpack hw p3.1 p3.2.1 p3p ht.2

@[expose] noncomputable def GSK (k : ℕ) : ℕ → ℕ :=
  if k = 0 then GS0 else if k = 1 then GS1 else GS2

theorem rGS {k : ℕ} (hk : k < 3) {j : ℕ} (hj : j < 4) : R (gensS k)[j]! (GSK k j) := by
  interval_cases k
  · exact ⟨hgS0 j hj, by interval_cases j <;> quickRfl⟩
  · exact ⟨hgS1 j hj, by interval_cases j <;> quickRfl⟩
  · exact ⟨hgS2 j hj, by interval_cases j <;> quickRfl⟩

theorem arrAll (a : Array (Array ℕ)) (F : Array ℕ → Bool) :
    a.all F = (List.range a.size).all fun j => F a[j]! := by
  apply Bool.eq_iff_iff.2
  simp only [Array.all_eq_true, List.all_eq_true, List.mem_range]
  constructor
  · intro h j hj
    rw [getElem!_pos a j hj]
    exact h j hj
  · intro h j hj
    have := h j hj
    rwa [getElem!_pos a j hj] at this

theorem gsAll (k : ℕ) (F : Array ℕ → Bool) :
    (gensS k).all F = (List.range 4).all fun j => F (gensS k)[j]! := by
  rw [arrAll, gs_size]

@[expose] noncomputable def twoK (p : ℕ) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => ℕ → ℕ) (fun q => q) (fun _ ih q => ih (cm q q)) 7 p) I

theorem _root_.CertificateChecks.KernelMisc.J2Fam.R.two {t : Array ℕ} {p : ℕ} (ht : R t p) :
    isTwoA t = twoK p := by
  unfold isTwoA twoK
  rw [ht.1, (sqIterU 7 p ht.2).1, ← hI, eqU (sqIterU 7 p ht.2).2 pI]

theorem rVW {k : ℕ} (hk : k < 12) : R vWits[k]! (J2Fam.VW k) := ⟨hvw k hk, pVW k hk⟩
theorem rTW {k : ℕ} (hk : k < 3) : R tripWit[k]! (J2Fam.TW k) := ⟨htw k hk, pTW k hk⟩
theorem rU4 {k : ℕ} (hk : k < 4) : R u34Gens[k]! (J2Fam.U4 k) := ⟨hu4 k hk, pU4 k hk⟩

theorem chkSConj_true : chkSConj = true := by
  unfold chkSConj
  refine List.all_eq_true.2 fun i hi => ?_
  have h3 := mem3 hi
  rw [inP3 (rCC h3), ((rCC h3).conj rX).eq ((rZ.pow i).comp rX)]
  interval_cases i <;> quickRfl

theorem chkSPieces_true : chkSPieces = true := by
  unfold chkSPieces
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [inS 0 (by norm_num) (rwg0 (i := 0) (by norm_num)),
    inS 0 (by norm_num) (rwg1 (i := 0) (by norm_num)),
    inS 1 (by norm_num) (rwg0 (i := 2) (by norm_num)),
    inS 1 (by norm_num) (rwg1 (i := 2) (by norm_num)),
    inS 2 (by norm_num) (rwg0 (i := 1) (by norm_num)),
    inS 2 (by norm_num) (rwg1 (i := 1) (by norm_num))]
  quickRfl

theorem chkSNorm_true : chkSNorm = true := by
  unfold chkSNorm
  refine List.all_eq_true.2 fun k hk => ?_
  have h3 := mem3 hk
  rw [gsAll]
  refine List.all_eq_true.2 fun j hj => ?_
  rw [List.mem_range] at hj
  rw [inS k h3 (rZ.conj (rGS h3 hj)), inS k h3 (rX.conj (rGS h3 hj))]
  interval_cases k <;> interval_cases j <;> quickRfl

theorem chkSVWits_true : chkSVWits = true := by
  unfold chkSVWits
  refine List.all_eq_true.2 fun m hm => ?_
  have hm3 : m < 3 := by simpa [vWitPairs] using hm
  have hi : (vWitPairs.getD m (0, 0)).1 < 3 := by interval_cases m <;> decide
  have hk : (vWitPairs.getD m (0, 0)).2 < 3 := by interval_cases m <;> decide
  have r0 := rVW (k := 4 * m) (by omega)
  have r1 := rVW (k := 4 * m + 1) (by omega)
  have r2 := rVW (k := 4 * m + 2) (by omega)
  have r3 := rVW (k := 4 * m + 3) (by omega)
  dsimp only
  rw [r0.memW hi, r1.memVk hk, r2.memW hi, r3.memVk hk, (r0.comp (r1.comp (r2.comp r3))).two]
  interval_cases m <;> quickRfl

theorem chkSTrip_true : chkSTrip = true := by
  unfold chkSTrip
  have r0 := rTW (k := 0) (by norm_num)
  have r1 := rTW (k := 1) (by norm_num)
  have r2 := rTW (k := 2) (by norm_num)
  rw [r0.memVk (by norm_num), r1.memVk (by norm_num), r2.memVk (by norm_num),
    (r0.comp (r1.comp r2)).two]
  quickRfl

theorem chkSDistinct_true : chkSDistinct = true := by
  unfold chkSDistinct
  rw [inS 1 (by norm_num) (J2Fam.rVK (k := 1) (by norm_num) 1),
    inS 2 (by norm_num) (J2Fam.rVK (k := 0) (by norm_num) 1),
    inS 0 (by norm_num) (J2Fam.rVK (k := 2) (by norm_num) 1)]
  quickRfl

theorem chkSCz_true : chkSCz = true :=
  (allLt_congr_of_mem (memCS 0 (by norm_num)) fun t => !(commA t zArr) || inW 0 t).trans
    chkSCz_lit

theorem chkSProd_true : chkSProd = true :=
  (allLt_congr_of_mem (memCS 0 (by norm_num)) fun t => (wElts 0).any fun w =>
    (List.range 4).any fun e => (List.range 4).any fun f =>
      eqA 315 t (compA 315 w (compA 315
        (conjA 315 cConj[0]! (if e = 0 then idA 315 else if e = 1 then v1Arr else
          if e = 2 then v2Arr else compA 315 v1Arr v2Arr))
        (conjA 315 cConj[1]! (if f = 0 then idA 315 else if f = 1 then v1Arr else
          if f = 2 then v2Arr else compA 315 v1Arr v2Arr))))).trans chkSProd_lit

@[expose] noncomputable def sp3K (q : ℕ) : Bool :=
  [0, 1, 2].any fun k => (List.range 4).all fun j =>
    memK 64 (lget (SPL k)) (cm (iv q) (cm (GSK 0 j) q))

theorem sp3All : ∀ m < 27, sp3K (J2C3.P3P.F m) = true :=
  (CFSG.KC.Misc.Clos.allN_iff _ _).1 (by quickRfl)

theorem chkSP3_true : chkSP3 = true := by
  unfold chkSP3
  rw [allLt_iff, p3.1]
  intro m hm
  have rm : R cP3.pts[m]! (J2C3.P3P.F m) := ⟨p3.2.1 m hm, p3p m hm⟩
  have h := sp3All m hm
  unfold sp3K at h
  refine Eq.trans (any_congr_mem fun k hk => ?_) h
  rw [gsAll]
  exact all_congr_mem fun j hj => by
    rw [List.mem_range] at hj
    exact inS k (mem3 hk) (rm.conjInv (rGS (by norm_num) hj))

theorem chkSP3Onto_true : chkSP3Onto = true := by
  unfold chkSP3Onto
  rw [p3.1]
  have h : ([0, 1, 2].all fun k => (List.range 27).any fun m => (List.range 4).all fun j =>
      memK 64 (lget (SPL k)) (cm (iv (J2C3.P3P.F m)) (cm (GSK 0 j) (J2C3.P3P.F m)))) = true := by
    quickRfl
  refine Eq.trans (all_congr_mem fun k hk => any_congr_mem fun m hm => ?_) h
  rw [List.mem_range] at hm
  have rm : R cP3.pts[m]! (J2C3.P3P.F m) := ⟨p3.2.1 m hm, p3p m hm⟩
  rw [gsAll]
  exact all_congr_mem fun j hj => by
    rw [List.mem_range] at hj
    exact inS k (mem3 hk) (rm.conjInv (rGS (by norm_num) hj))

theorem chkSU_true : chkSU = true := by
  unfold chkSU
  have h : ((List.range 4).all fun j => memK 64 (lget (SPL 0)) (J2Fam.U4 j)) = true := by quickRfl
  refine Eq.trans (all_congr_mem fun j hj => ?_) h
  rw [List.mem_range] at hj
  exact inS 0 (by norm_num) (rU4 hj)

theorem chkS_true : chkS = true := by
  unfold chkS
  rw [chkSConj_true, chkSPieces_true, chkSNorm_true, chkSVWits_true, chkSTrip_true,
    chkSDistinct_true, chkSCz_true, chkSProd_true, chkSP3_true, chkSP3Onto_true, chkSU_true,
    chkSLaw_true]
  rfl

theorem anyConj {e t : ℕ} (pe : permB 315 9 e = true) (pt : permB 315 9 t = true) :
    (aElts.any fun f => eqA 315 (conjA 315 f (unpack 315 9 e)) (unpack 315 9 t)) =
      AEK.any fun f => Nat.beq (cj f e) t := by
  rw [hae]
  exact any_map_congr fun f hf => by rw [conjU (pAE f hf) pe, eqU (pcj (pAE f hf) pe) pt]

theorem phT_ne {a b c a' b' c' : ℕ} (ha : a < 4) (hb : b < 4) (hc : c < 4) (ha' : a' < 4)
    (hb' : b' < 4) (hc' : c' < 4) (h : ¬(a = a' ∧ b = b' ∧ c = c')) :
    Nat.beq (phT a b c) (phT a' b' c') = false := by
  unfold phT
  have hne : 16 * a + 4 * b + c ≠ 16 * a' + 4 * b' + c' := by omega
  have key : ∀ i j, i < 64 → j < i → lget PH i ≠ lget PH j := by
    intro i j hi hj e
    have h' := (CFSG.KC.Misc.Clos.allN_iff _ _).1 (phDAll i hi) j hj
    rw [e, Nat.beq_refl] at h'
    exact absurd h' (by decide)
  have hne' : lget PH (16 * a + 4 * b + c) ≠ lget PH (16 * a' + 4 * b' + c') := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact fun e => key _ _ (by omega) hlt e.symm
    · exact key _ _ (by omega) hlt
  cases hq : Nat.beq (lget PH (16 * a + 4 * b + c)) (lget PH (16 * a' + 4 * b' + c'))
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hq) hne'

theorem chkVk_true : chkVk = true := by
  unfold chkVk
  have h1 : (aElts.all fun f => validA 315 f) = true := by
    refine List.all_eq_true.2 fun f hf => ?_
    rw [hae] at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
    exact J2Fam.R.valid ⟨rfl, pAE g hg⟩
  have h2 : allLt vWits.size (fun k => okA vWits[k]!) = true := by
    rw [allLt_iff, vw_size]
    exact okvw
  have h3 : allLt tripWit.size (fun k => okA tripWit[k]!) = true := by
    rw [allLt_iff, tw_size]
    exact oktw
  have h4 : ([0, 1, 2].all fun k =>
      [vkArr k 1, vkArr k 2, compA 315 (vkArr k 1) (vkArr k 2)].all fun e =>
        (aElts.any fun f => eqA 315 (conjA 315 f e) (vkArr k 1)) &&
          (aElts.any fun f => eqA 315 (conjA 315 f e) (vkArr k 2))) = true := by
    refine List.all_eq_true.2 fun k hk => ?_
    have h3 := mem3 hk
    have r1 := J2Fam.rVK h3 1
    have r2 := J2Fam.rVK h3 2
    have r12 := r1.comp r2
    rw [r12.1, r1.1, r2.1]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [anyConj r1.2 r1.2, anyConj r1.2 r2.2, anyConj r2.2 r1.2, anyConj r2.2 r2.2,
      anyConj r12.2 r1.2, anyConj r12.2 r2.2]
    interval_cases k <;> quickRfl
  have h5 : ((List.range 4).all fun a => (List.range 4).all fun b => (List.range 4).all fun c =>
      (List.range 4).all fun a' => (List.range 4).all fun b' => (List.range 4).all fun c' =>
        (a == a' && b == b' && c == c') || !(eqA 315 (phiA a b c) (phiA a' b' c'))) = true := by
    simp only [List.all_eq_true, List.mem_range]
    intro a ha b hb c hc a' ha' b' hb' c' hc'
    rw [phiKU, phiKU, eqU (pphi a b c) (pphi a' b' c'), ← phTeq ha hb hc, ← phTeq ha' hb' hc']
    by_cases h : a = a' ∧ b = b' ∧ c = c'
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp
    · rw [phT_ne ha hb hc ha' hb' hc' h]
      simp
  rw [h1, h2, h3, h4, h5]
  rfl

theorem neg_memS : (!memK 64 (lget (SPL 0)) X) = true := by quickRfl

theorem neg_two : (!twoK X) = true := by quickRfl

theorem neg_gen : (!memK 64 (lget (SPL 0)) (GSK 1 2)) = true := by quickRfl


end CertificateChecks.KernelMisc.J2En

end
