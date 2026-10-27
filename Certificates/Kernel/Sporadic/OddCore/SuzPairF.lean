module

public import Certificates.Kernel.Sporadic.OddCore.SuzPairC
public import Certificates.Kernel.Sporadic.OddCore.SuzRFF
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzPair

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.LocalR CFSG.ComponentClassification.AS81.SuzB0
  CFSG.PSL3Four.Native CFSG.Sporadic.SuzOddCore CFSG.LocalAnalysis.WeakClosure81.SporSuz
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzRF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "Id" => pidn 1782 11
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "T1" => SuzInvT1.F 0

theorem allN_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) : allN n f = allN n g := by
  refine Bool.eq_iff_iff.2 ?_
  rw [CFSG.KS.Raw.Orb.allN_iff, CFSG.KS.Raw.Orb.allN_iff]
  exact ⟨fun h' i hi => (h i hi) ▸ h' i hi, fun h' i hi => (h i hi).symm ▸ h' i hi⟩

theorem all_gens (f : Tab → Bool) : s1Gens.all f = allN 4 (fun j => f s1Gens[j]!) := by
  refine Bool.eq_iff_iff.2 ?_
  rw [Array.all_eq_true, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro h j hj
    rw [getElem!_pos s1Gens j (by rw [gS.1]; exact hj)]
    exact h j _
  · intro h j hj
    have e := h j (by rw [← gS.1]; exact hj)
    rwa [getElem!_pos s1Gens j hj] at e

theorem pGen {j : Nat} (hj : j < 4) : P s1Gens[j]! (SuzRFS.G j) := gS.2 j hj

theorem tabs_size : s1Enum.tabs.size = 8192 := by
  unfold s1Enum
  rw [sE.1, rec_size, kCnt.2.2.2.2]

theorem pT {k : Nat} (hk : k < 8192) : P s1Enum.tabs[k]! (SuzRFS.T k) := by
  unfold s1Enum
  rw [sE.1, rec_tabs (by rw [kCnt.2.2.2.2]; exact hk)]
  exact ⟨rfl, canS hk⟩

theorem inv5 : ie Suz2306.B0 (SuzPairT 0) = true ∧ ie Suz2306.B1 (SuzPairT 1) = true ∧
    ie (SuzInvT1.F 20) (SuzPairT 2) = true ∧ ie (SuzInvT1.F 22) (SuzPairT 3) = true ∧
    ie (SuzPairT 4) (SuzPairT 5) = true := by
  have h := kInv
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem canT {i : Nat} (hi : i < 6) : cn (SuzPairT i) = true := allN_spec kCan i hi

theorem pAB {j : Nat} (hj : j < 2) : P (abG j) (abK j) := by
  interval_cases j
  · exact pB0
  · exact pB1

theorem pABI {j : Nat} (hj : j < 2) : P (abI j) (abIK j) := by
  interval_cases j
  · exact (p_invR (pAB (j := 0) (by norm_num)) inv5.1 (canT (i := 0) (by norm_num))).1
  · exact (p_invR (pAB (j := 1) (by norm_num)) inv5.2.1 (canT (i := 1) (by norm_num))).1

theorem letters : (∀ z ∈ gWord, z.natAbs - 1 < 2) ∧ (∀ z ∈ b0Word, z.natAbs - 1 < 3) ∧
    ∀ z ∈ b1Word, z.natAbs - 1 < 3 := by
  have h : lettersOK () = true := by decide
  simp only [lettersOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem iw_P {gs gis : Nat → Tab} {G GI : Nat → Nat} {k : Nat} (hg : ∀ j < k, P (gs j) (G j))
    (hgi : ∀ j < k, P (gis j) (GI j)) :
    ∀ w : List Int, (∀ z ∈ w, z.natAbs - 1 < k) → P (evalW gs gis w) (iwK G GI w)
  | [], _ => pId'
  | z :: w, h => by
    have hz := h z List.mem_cons_self
    have hl : P (if 0 < z then gs (z.natAbs - 1) else gis (z.natAbs - 1)) (ltK G GI z) := by
      rcases z with (_ | n) | m
      · exact hgi 0 hz
      · have e : (0 : Int) < Int.ofNat (n + 1) := Int.ofNat_lt.2 (Nat.succ_pos n)
        rw [if_pos e]
        exact hg n hz
      · have e : ¬ (0 : Int) < Int.negSucc m := fun h => absurd h (Int.not_lt.2 (Int.negSucc_lt_zero m).le)
        rw [if_neg e]
        exact hgi m hz
    unfold evalW iwK
    rw [List.foldr_cons]
    exact pc' hl (iw_P hg hgi w fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem pG : P (gTab ()) (SuzPairT 4) := p_eq (iw_P (fun j hj => pAB hj) (fun j hj => pABI hj)
  gWord letters.1) kG

theorem pCG {j : Nat} (hj : j < 3) : P (cgG j) (cgK j) := by
  interval_cases j
  · exact pC (k := 2) (by norm_num)
  · exact pC (k := 4) (by norm_num)
  · exact pG

theorem pCGI {j : Nat} (hj : j < 3) : P (cgI j) (cgIK j) := by
  interval_cases j
  · exact (p_invR (pCG (j := 0) (by norm_num)) inv5.2.2.1 (canT (i := 2) (by norm_num))).1
  · exact (p_invR (pCG (j := 1) (by norm_num)) inv5.2.2.2.1 (canT (i := 3) (by norm_num))).1
  · exact (p_invR (pCG (j := 2) (by norm_num)) inv5.2.2.2.2 (canT (i := 5) (by norm_num))).1

theorem commT_P {x y : Tab} {X Y : Nat} (hx : P x X) (hy : P y Y) :
    commT x y = Nat.beq (pc X Y) (pc Y X) := by
  unfold commT
  exact beqP (pc' hx hy) (pc' hy hx)

theorem commZT_P {x y : Tab} {X Y : Nat} (hx : P x X) (hy : P y Y) :
    commZT x y = Nat.beq (pc X Y) (pc T1 (pc Y X)) := by
  unfold commZT
  exact beqP (pc' hx hy) (pc' pt1 (pc' hy hx))

theorem wit {k : Nat} (hk : k < 8192) :
    zK (SuzRFS.T k) (wg SuzPairWZ k) = true ∧ z2K (SuzRFS.T k) (wg SuzPairW2 k) = true := by
  have hs : k / 32 < 256 := by omega
  have h := allBlk_spec (w75343All (k / 32) hs) (k % 32) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 32 (k / 32)) (k % 32) = k := Nat.div_add_mod k 32
  rw [e] at h
  have h2 : strictB (SuzRFS.T k) (fun X =>
      bAnd(zK X (wg SuzPairWZ k), z2K X (wg SuzPairW2 k))) = true := h
  simp only [sB] at h2
  exact band h2

theorem ne_of_neC {X Y p : Nat} (hX : cn X = true) (hY : cn Y = true) (hp : p < 1782)
    (h : neC X Y p = true) : Nat.beq (pc X Y) (pc Y X) = false := by
  refine beq_false fun e => not_beq h ?_
  rw [← pg_pc hX hY hp, e, pg_pc hY hX hp]

theorem ne_of_neZ {X Y q : Nat} (hX : cn X = true) (hY : cn Y = true) (hq : q < 1782)
    (h : neZ X Y q = true) : Nat.beq (pc X Y) (pc T1 (pc Y X)) = false := by
  have hYX : cn (pc Y X) = true := (pc' (a := unpack 1782 11 Y) (b := unpack 1782 11 X)
    ⟨rfl, hY⟩ ⟨rfl, hX⟩).2
  refine beq_false fun e => not_beq h ?_
  rw [← pg_pc hX hY hq, e, pg_pc pt1.2 hYX hq, pg_pc hY hX hq]

theorem zK_sound {X e : Nat} (hX : cn X = true) (h : zK X e = true) :
    allN 4 (fun j => Nat.beq (pc X (SuzRFS.G j)) (pc (SuzRFS.G j) X)) = Nat.beq e 0 := by
  unfold zK at h
  by_cases h0 : e = 0
  · have hb : Nat.beq e 0 = true := by rw [h0]; rfl
    rw [bif_t hb h, hb]
  · have h' := bif_f (beq_false h0) h
    simp only [sB] at h'
    obtain ⟨hj, h2⟩ := band h'
    obtain ⟨hp, hn⟩ := band h2
    have hj' := Nat.blt_eq.mp hj
    rw [beq_false h0]
    refine Bool.eq_false_iff.2 fun ha => ?_
    have hc := CFSG.KS.Raw.Orb.allN_iff.1 ha _ hj'
    rw [ne_of_neC hX (pGen hj').2 (Nat.blt_eq.mp hp) hn] at hc
    exact absurd hc (by decide)

theorem z2K_sound {X e : Nat} (hX : cn X = true) (h : z2K X e = true) :
    allN 4 (fun j => Nat.beq (pc X (SuzRFS.G j)) (pc (SuzRFS.G j) X) ||
      Nat.beq (pc X (SuzRFS.G j)) (pc T1 (pc (SuzRFS.G j) X))) = Nat.beq e 0 := by
  unfold z2K at h
  by_cases h0 : e = 0
  · have hb : Nat.beq e 0 = true := by rw [h0]; rfl
    rw [bif_t hb h, hb]
  · have h' := bif_f (beq_false h0) h
    simp only [sB] at h'
    obtain ⟨hj, h2⟩ := band h'
    obtain ⟨hp, h3⟩ := band h2
    obtain ⟨hq, h4⟩ := band h3
    obtain ⟨hn, hz⟩ := band h4
    have hj' := Nat.blt_eq.mp hj
    rw [beq_false h0]
    refine Bool.eq_false_iff.2 fun ha => ?_
    have hc := CFSG.KS.Raw.Orb.allN_iff.1 ha _ hj'
    rw [ne_of_neC hX (pGen hj').2 (Nat.blt_eq.mp hp) hn,
      ne_of_neZ hX (pGen hj').2 (Nat.blt_eq.mp hq) hz] at hc
    exact absurd hc (by decide)

theorem sizes_true : sizesOK () = true := by
  unfold sizesOK
  rw [sizeP pt1, sizeP pB0, sizeP pB1, sizeP (pC (k := 2) (by norm_num)),
    sizeP (pC (k := 4) (by norm_num))]
  rfl

theorem letters_true : lettersOK () = true := by decide

theorem inverse_true : inverseTabsOK () = true := by
  have h := kInvW
  rw [Bool.and_eq_true] at h
  unfold inverseTabsOK
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun j hj => ?_, List.all_eq_true.2 fun j hj => ?_⟩
  · have hj' := List.mem_range.1 hj
    rw [sizeP (pABI hj'), beqP (pc' (pABI hj') (pAB hj')) pId', allN_spec h.1 j hj']
    rfl
  · have hj' := List.mem_range.1 hj
    rw [sizeP (pCGI hj'), beqP (pc' (pCGI hj') (pCG hj')) pId', allN_spec h.2 j hj']
    rfl

theorem enum_true : s1EnumOK () = true := by
  have h := kE
  rw [Bool.and_eq_true] at h
  unfold s1EnumOK s1PosT
  rw [tabs_size, beqP (pT (k := 0) (by norm_num)) pId', beqP (pT (k := 174) (by norm_num)) pt1,
    h.1, h.2]
  rfl

theorem center_true : centerOK () = true := by
  unfold centerOK s1PosT
  rw [List.filter_congr (q := fun k => Nat.beq (wg SuzPairWZ k) 0) fun k hk => ?_, sel_spec kSelZ]
  · rfl
  · have hk' := List.mem_range.1 hk
    rw [all_gens, allN_congr (g := fun j => Nat.beq (pc (SuzRFS.T k) (SuzRFS.G j))
      (pc (SuzRFS.G j) (SuzRFS.T k))) fun j hj => commT_P (pT hk') (pGen hj)]
    exact zK_sound (canS hk') (wit hk').1

theorem z2_true : z2OK () = true := by
  unfold z2OK s1PosT s1PosV s1PosW
  rw [List.filter_congr (q := fun k => Nat.beq (wg SuzPairW2 k) 0) fun k hk => ?_, sel_spec kSel2]
  · rfl
  · have hk' := List.mem_range.1 hk
    rw [all_gens, allN_congr (g := fun j => Nat.beq (pc (SuzRFS.T k) (SuzRFS.G j))
      (pc (SuzRFS.G j) (SuzRFS.T k)) || Nat.beq (pc (SuzRFS.T k) (SuzRFS.G j))
        (pc T1 (pc (SuzRFS.G j) (SuzRFS.T k)))) fun j hj => by
      rw [commT_P (pT hk') (pGen hj), commZT_P (pT hk') (pGen hj)]]
    exact z2K_sound (canS hk') (wit hk').2

theorem inV_P {g x : Tab} {G X : Nat} (hg : P g G) (hx : P x X) : conjInV g x = inVK G X := by
  unfold conjInV inVK s1PosT s1PosV s1PosW
  simp only [List.any_cons, List.any_nil]
  rw [beqP (pc' hg hx) (pc' (pT (k := 174) (by norm_num)) hg),
    beqP (pc' hg hx) (pc' (pT (k := 8113) (by norm_num)) hg),
    beqP (pc' hg hx) (pc' (pT (k := 8149) (by norm_num)) hg)]

theorem gNorm_true : gNormOK () = true := by
  unfold gNormOK
  rw [inV_P pG pt1, s1PosV, inV_P pG (pT (k := 8113) (by norm_num)), commT_P pG pt1]
  exact kGN

theorem gen_true : genOK () = true := by
  unfold genOK
  rw [beqP (iw_P (fun j hj => pCG hj) (fun j hj => pCGI hj) b0Word letters.2.1) pB0,
    beqP (iw_P (fun j hj => pCG hj) (fun j hj => pCGI hj) b1Word letters.2.2) pB1]
  exact kGen

theorem pair_true : suzPairOK () = true := by
  unfold suzPairOK
  rw [sizes_true, letters_true, inverse_true, enum_true, center_true, z2_true, gNorm_true,
    gen_true]
  rfl

end CertificateChecks.KernelSpor.SuzPair

end
