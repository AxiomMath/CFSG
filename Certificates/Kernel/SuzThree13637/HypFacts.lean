
module

public import Certificates.Kernel.SuzThree13637.Hyp
public import Certificates.Kernel.SuzThree13637.HypAux
public import Certificates.Kernel.SuzThree13637.BindFacts
public import CFSG.Certificates.Kernel.Spor.PSearchSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeBase
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.AbelianSylow
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzOuter
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringDoubleCover
public import CFSG.Sporadic.FischerOddCore.AlmostSimple
public import CFSG.Sporadic.FischerOddCore.PairComp
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CFSG.KD.SuzThree13637

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PSearch CFSG.KS.HypK
  CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CertificateChecks.KernelSpor
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
  CFSG.RankThree.Native
open CFSG.Sporadic.SuzOddCore (suzM smallChain smallChain_arrays smallChain_check smallChain_valid
  smallChain_originalSubgroup mem_suzM_iff_siftA smallStrongArrs smallBaseNat)
open CFSG.Monster.B.Co2 (permOfArr)

theorem n32_13637 : (1782 : ℕ) < 2 ^ 32 := by norm_num

theorem prep_of_permB13637 {p : ℕ} (hp : permB 1782 11 p = true) :
    PRep 1782 11 p (permOfArr 1782 (unpack 1782 11 p)) :=
  prep_of_rep (rep_of_validA (validA_of hp))

theorem prep_eq13637 {P : ℕ} {g h : Equiv.Perm (Fin 1782)} (hg : PRep 1782 11 P g)
    (hh : PRep 1782 11 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem mem_of_inPK {g : ℕ}
    (h : inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP g = true) :
    permB 1782 11 g = true ∧ permOfArr 1782 (unpack 1782 11 g) ∈ suzM := by
  unfold inPK at h
  rw [bAnd_eqS, Bool.and_eq_true] at h
  obtain ⟨hp, hs⟩ := h
  refine ⟨hp, (mem_suzM_iff_siftA (rep_of_validA (validA_of hp))).1 ?_⟩
  obtain ⟨h1, -, h3⟩ := permOK_facts (n := 1782) (w := 11) hp
  exact siftA_of Suz2306.binds Suz2306.perm SuzC.hl
    ⟨by rw [h1]; rfl, allN_iff.2 fun i hi => by rw [Nat.blt_eq]; exact (h3 i hi).1, hs⟩

theorem prep_d {i : ℕ} (hi : i < 5) : PRep 1782 11 (nthN F.D i) (dPerm ⟨i, hi⟩) := by
  obtain ⟨e, p⟩ := d_gen hi
  have h : dPerm ⟨i, hi⟩ = permOfArr 1782 (unpack 1782 11 (nthN F.D i)) := by
    unfold dPerm
    rw [e]
  rw [h]
  exact prep_of_permB13637 p

theorem d_parts {i : ℕ} (hi : i < 5) :
    inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP (nthN F.D i) = true ∧
    pcomp 1782 11 (mask 11) (nthN F.D i) (pcomp 1782 11 (mask 11) (nthN F.D i) (nthN F.D i)) =
      pidn 1782 11 ∧
    ∀ j < 5, pcomp 1782 11 (mask 11) (nthN F.D i) (nthN F.D j) =
      pcomp 1782 11 (mask 11) (nthN F.D j) (nthN F.D i) := by
  have h0 := d_ok
  unfold dOK at h0
  have h := allN_iff.1 h0 i hi
  rw [Orb.strictB_eq, bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, fun j hj => ?_⟩
  have h2 := allN_iff.1 h.2.2 j hj
  rw [Orb.strictB_eq] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem dK_pow (i : Fin 5) : dPerm i ^ 3 = 1 := by
  have hd := prep_d i.2
  have h1 := prep_pcomp n32_13637 hd (prep_pcomp n32_13637 hd hd)
  rw [(d_parts i.2).2.1] at h1
  rw [pow_three]
  exact prep_eq13637 h1 (prep_pidn (by norm_num) (by norm_num))

theorem dK_comm (i j : Fin 5) : Commute (dPerm i) (dPerm j) := by
  have hi := prep_d i.2
  have hj := prep_d j.2
  have h1 := prep_pcomp n32_13637 hi hj
  rw [(d_parts i.2).2.2 j j.2] at h1
  exact prep_eq13637 h1 (prep_pcomp n32_13637 hj hi)

theorem dK_mem (i : Fin 5) :
    dPerm i ∈ suzM := by
  obtain ⟨p, hm⟩ := mem_of_inPK (d_parts i.2).1
  rw [prep_eq13637 (prep_d i.2) (prep_of_permB13637 p)]
  exact hm

@[expose] noncomputable def φK : Multiplicative (Fin 5 → ZMod 3) →* Equiv.Perm (Fin 1782) :=
  Co3T.vecProdHom dPerm dK_comm dK_pow

@[expose] noncomputable def DK : Subgroup (Equiv.Perm (Fin 1782)) := φK.range

theorem φK_vec (k : ℕ) : φK (Multiplicative.ofAdd (vec k)) =
    dPerm 0 ^ digit3 k 0 * (dPerm 1 ^ digit3 k 1 * (dPerm 2 ^ digit3 k 2 *
      (dPerm 3 ^ digit3 k 3 * dPerm 4 ^ digit3 k 4))) := by
  unfold φK
  rw [Co3T.vecProdHom_apply, vecProd_eq]
  simp only [vec_val]
  rfl

theorem prep_mulD {d x a : ℕ} {Dp X : Equiv.Perm (Fin 1782)} (hd : PRep 1782 11 d Dp)
    (hx : PRep 1782 11 x X) (ha : a < 3) : PRep 1782 11 (mulD 1782 11 d a x) (Dp ^ a * X) := by
  interval_cases a
  · change PRep 1782 11 x _
    simpa using hx
  · change PRep 1782 11 (pcomp 1782 11 (mask 11) d x) _
    simpa using prep_pcomp n32_13637 hd hx
  · change PRep 1782 11 (strictN (pcomp 1782 11 (mask 11) d x) (pcomp 1782 11 (mask 11) d)) _
    rw [strictN_eq, pow_two, mul_assoc]
    exact prep_pcomp n32_13637 hd (prep_pcomp n32_13637 hd hx)

theorem dg3_lt (k t : ℕ) : dg3 k t < 3 := Nat.mod_lt _ (by norm_num)

theorem prep_ePg {x : ℕ} {X : Equiv.Perm (Fin 1782)} (hx : PRep 1782 11 x X) (k : ℕ) :
    PRep 1782 11 (ePg 1782 11 F.D k x) (φK (Multiplicative.ofAdd (vec k)) * X) := by
  unfold ePg
  simp only [strictN_eq]
  have h4 := prep_mulD (prep_d (i := 4) (by norm_num)) hx (dg3_lt k 4)
  have h3 := prep_mulD (prep_d (i := 3) (by norm_num)) h4 (dg3_lt k 3)
  have h2 := prep_mulD (prep_d (i := 2) (by norm_num)) h3 (dg3_lt k 2)
  have h1 := prep_mulD (prep_d (i := 1) (by norm_num)) h2 (dg3_lt k 1)
  have h0 := prep_mulD (prep_d (i := 0) (by norm_num)) h1 (dg3_lt k 0)
  rw [φK_vec]
  simp only [mul_assoc]
  exact h0

theorem ev1_eq {d a : ℕ} {Dp : Equiv.Perm (Fin 1782)} (hd : PRep 1782 11 d Dp) (ha : a < 3)
    (x : Fin 1782) : ev1 11 d a x = ((Dp ^ a) x : ℕ) := by
  interval_cases a
  · change (x : ℕ) = _
    simp
  · change pg 11 (mask 11) d x = _
    rw [hd x, pow_one]
  · change pg 11 (mask 11) d (pg 11 (mask 11) d x) = _
    rw [hd x, hd (Dp x), pow_two, Equiv.Perm.mul_apply]

theorem evD_eq (k : ℕ) (x : Fin 1782) :
    evD 11 F.D k x = ((φK (Multiplicative.ofAdd (vec k))) x : ℕ) := by
  have e : evD 11 F.D k x = ev1 11 (nthN F.D 0) (digit3 k 0) (ev1 11 (nthN F.D 1) (digit3 k 1)
      (ev1 11 (nthN F.D 2) (digit3 k 2) (ev1 11 (nthN F.D 3) (digit3 k 3)
        (ev1 11 (nthN F.D 4) (digit3 k 4) x)))) := rfl
  have p0 : PRep 1782 11 (nthN F.D 0) (dPerm 0) := prep_d (by norm_num)
  have p1 : PRep 1782 11 (nthN F.D 1) (dPerm 1) := prep_d (by norm_num)
  have p2 : PRep 1782 11 (nthN F.D 2) (dPerm 2) := prep_d (by norm_num)
  have p3 : PRep 1782 11 (nthN F.D 3) (dPerm 3) := prep_d (by norm_num)
  have p4 : PRep 1782 11 (nthN F.D 4) (dPerm 4) := prep_d (by norm_num)
  have hl : ∀ t, digit3 k t < 3 := fun t => dg3_lt k t
  rw [e, ev1_eq p4 (hl 4), ev1_eq p3 (hl 3), ev1_eq p2 (hl 2), ev1_eq p1 (hl 1), ev1_eq p0 (hl 0),
    φK_vec]
  simp only [Equiv.Perm.mul_apply]

theorem d_inj_at {k : ℕ} (hk : k < 243) (h0 : k ≠ 0) :
    evD 11 F.D k 0 ≠ 0 ∨ evD 11 F.D k 2 ≠ 2 := by
  have hh := d_inj
  unfold dInjOK at hh
  have h := allN_iff.1 hh k hk
  by_contra hc
  push Not at hc
  have h' : bIf(Nat.beq k 0, true, bIf(Nat.beq (evD 11 F.D k 0) 0,
      bIf(Nat.beq (evD 11 F.D k 2) 2, false, true), true)) = true := h
  cases hb : Nat.beq k 0
  · rw [hb, hc.1, hc.2] at h'
    exact absurd h' (by decide)
  · exact h0 (Nat.eq_of_beq_eq_true hb)

theorem idx_vec13637 {k : ℕ} (hk : k < 243) : idx (vec k) = k := by
  unfold idx
  simp only [vec_val]
  simp only [digit3, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, Nat.div_one]
  norm_num
  omega

theorem φK_injective : Function.Injective φK := by
  rw [injective_iff_map_eq_one]
  intro a ha
  set k := idx (Multiplicative.toAdd a) with hkdef
  have hk : k < 243 := idx_lt _
  have hav : a = Multiplicative.ofAdd (vec k) := by rw [hkdef, vec_idx, ofAdd_toAdd]
  by_cases h0 : k = 0
  · rw [hav, h0]
    apply Multiplicative.toAdd.injective
    funext i
    simp [vec, digit3]
  · exfalso
    rw [hav] at ha
    have e0 : evD 11 F.D k 0 = ((φK (Multiplicative.ofAdd (vec k))) 0 : ℕ) := evD_eq k 0
    have e2 : evD 11 F.D k 2 = ((φK (Multiplicative.ofAdd (vec k))) 2 : ℕ) := evD_eq k 2
    rw [ha] at e0 e2
    rcases d_inj_at hk h0 with h | h
    · exact h (by rw [e0]; rfl)
    · exact h (by rw [e2]; rfl)

theorem card_DK : Nat.card DK = 243 := by
  rw [DK, MonoidHom.range_eq_map, Subgroup.card_map_of_injective φK_injective, Subgroup.card_top,
    Co3T.card_vec]
  norm_num

theorem DK_comm : ∀ x ∈ DK, ∀ y ∈ DK, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem DK_le : DK ≤ suzM := by
  rintro _ ⟨a, rfl⟩
  change Co3T.vecProd dPerm a.toAdd ∈ suzM
  rw [vecProd_eq]
  have h := dK_mem
  exact suzM.mul_mem (suzM.pow_mem (h 0) _) (suzM.mul_mem (suzM.pow_mem (h 1) _)
    (suzM.mul_mem (suzM.pow_mem (h 2) _) (suzM.mul_mem (suzM.pow_mem (h 3) _)
      (suzM.pow_mem (h 4) _))))

theorem mem_DK (k : ℕ) : φK (Multiplicative.ofAdd (vec k)) ∈ DK := ⟨_, rfl⟩

theorem DK_eq {x : Equiv.Perm (Fin 1782)} (hx : x ∈ DK) :
    ∃ k < 243, x = φK (Multiplicative.ofAdd (vec k)) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨idx a.toAdd, idx_lt _, by rw [vec_idx, ofAdd_toAdd]⟩

theorem digit3_five {c0 c1 c2 c3 c4 : ℕ} (h0 : c0 < 3) (h1 : c1 < 3) (h2 : c2 < 3) (h3 : c3 < 3)
    (h4 : c4 < 3) :
    digit3 (c0 + 3 * (c1 + 3 * (c2 + 3 * (c3 + 3 * c4)))) 0 = c0 ∧
    digit3 (c0 + 3 * (c1 + 3 * (c2 + 3 * (c3 + 3 * c4)))) 1 = c1 ∧
    digit3 (c0 + 3 * (c1 + 3 * (c2 + 3 * (c3 + 3 * c4)))) 2 = c2 ∧
    digit3 (c0 + 3 * (c1 + 3 * (c2 + 3 * (c3 + 3 * c4)))) 3 = c3 ∧
    digit3 (c0 + 3 * (c1 + 3 * (c2 + 3 * (c3 + 3 * c4)))) 4 = c4 := by
  simp only [digit3, Nat.reducePow, Nat.div_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega

theorem act5_digit (M : List ℕ) (k : ℕ) (t : Fin 5) : digit3 (act5 M k) t = actC M k t := by
  have hc : ∀ t, actC M k t < 3 := fun t => Nat.mod_lt _ (by norm_num)
  have e : act5 M k = actC M k 0 + 3 * (actC M k 1 + 3 * (actC M k 2 + 3 * (actC M k 3 +
      3 * actC M k 4))) := rfl
  obtain ⟨h0, h1, h2, h3, h4⟩ := digit3_five (hc 0) (hc 1) (hc 2) (hc 3) (hc 4)
  rw [e]
  fin_cases t
  exacts [h0, h1, h2, h3, h4]

theorem act5_lt (M : List ℕ) (k : ℕ) : act5 M k < 243 := by
  have hc : ∀ t, actC M k t < 3 := fun t => Nat.mod_lt _ (by norm_num)
  have e : act5 M k = actC M k 0 + 3 * (actC M k 1 + 3 * (actC M k 2 + 3 * (actC M k 3 +
      3 * actC M k 4))) := rfl
  have := hc 0
  have := hc 1
  have := hc 2
  have := hc 3
  have := hc 4
  omega

theorem vec_act5 (M : List ℕ) (k : ℕ) : vec (act5 M k) =
    digit3 k 0 • vec (nthN M 0) + (digit3 k 1 • vec (nthN M 1) + (digit3 k 2 • vec (nthN M 2) +
      (digit3 k 3 • vec (nthN M 3) + digit3 k 4 • vec (nthN M 4)))) := by
  funext t
  simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, vec]
  rw [act5_digit]
  have e : actC M k t = (digit3 k 0 * digit3 (nthN M 0) t + (digit3 k 1 * digit3 (nthN M 1) t +
      (digit3 k 2 * digit3 (nthN M 2) t + (digit3 k 3 * digit3 (nthN M 3) t +
        digit3 k 4 * digit3 (nthN M 4) t)))) % 3 := rfl
  rw [e, ZMod.natCast_mod]
  push_cast
  ring

theorem vec_dbl5 (x : ℕ) : vec (dbl5 x) = 2 • vec x := by
  have hc : ∀ t, 2 * digit3 x t % 3 < 3 := fun t => Nat.mod_lt _ (by norm_num)
  have e : dbl5 x = 2 * digit3 x 0 % 3 + 3 * (2 * digit3 x 1 % 3 + 3 * (2 * digit3 x 2 % 3 +
      3 * (2 * digit3 x 3 % 3 + 3 * (2 * digit3 x 4 % 3)))) := rfl
  obtain ⟨h0, h1, h2, h3, h4⟩ := digit3_five (hc 0) (hc 1) (hc 2) (hc 3) (hc 4)
  funext t
  simp only [Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.ofNat_apply, Pi.natCast_apply, vec]
  rw [e]
  fin_cases t <;> simp only [h0, h1, h2, h3, h4] <;> rw [ZMod.natCast_mod] <;> push_cast <;> rfl

theorem dot5_iff (m k : ℕ) : dot5 m k = 0 ↔ ∑ i, vec m i * vec k i = 0 := by
  have e : dot5 m k = (digit3 m 0 * digit3 k 0 + (digit3 m 1 * digit3 k 1 + (digit3 m 2 * digit3 k 2 +
      (digit3 m 3 * digit3 k 3 + digit3 m 4 * digit3 k 4)))) % 3 := rfl
  have hs : ∑ i, vec m i * vec k i = ((digit3 m 0 * digit3 k 0 + (digit3 m 1 * digit3 k 1 +
      (digit3 m 2 * digit3 k 2 + (digit3 m 3 * digit3 k 3 + digit3 m 4 * digit3 k 4))) : ℕ) :
        ZMod 3) := by
    simp only [Fin.sum_univ_five, vec]
    push_cast
    ring_nf
    rfl
  rw [e, hs, ← ZMod.val_natCast, ZMod.val_eq_zero]

theorem dot5_canon {x k : ℕ} (h : dot5 (canon5 x) k = 0) : ∑ i, vec x i * vec k i = 0 := by
  rw [dot5_iff] at h
  cases hb : Nat.beq (lead5 x) 1
  · have e : canon5 x = dbl5 x := by
      unfold canon5
      rw [hb]
    rw [e, vec_dbl5] at h
    have h2 : (2 : ZMod 3) * ∑ i, vec x i * vec k i = 0 := by
      rw [Finset.mul_sum]
      simpa [Pi.smul_apply, nsmul_eq_mul, Pi.mul_apply, Pi.ofNat_apply, mul_assoc] using h
    have h4 : (2 : ZMod 3) * 2 = 1 := by decide
    calc ∑ i, vec x i * vec k i = (2 * 2) * ∑ i, vec x i * vec k i := by rw [h4, one_mul]
      _ = 0 := by rw [mul_assoc, h2, mul_zero]
  · have e : canon5 x = x := by
      unfold canon5
      rw [hb]
    rwa [e] at h

theorem n_parts {i : ℕ} (hi : i < 2) : ∃ q : ℕ, inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP q = true ∧
    ∀ l < 5, pcomp 1782 11 (mask 11) q (nthN F.D l) =
      ePg 1782 11 F.D (nthN (nthL F.M i) l) q := by
  have h0 := n_ok
  unfold nOK at h0
  have h := allN_iff.1 h0 i hi
  unfold withReb at h
  rcases e : rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => nthN (nthL F.nb i) l) 6 with
    ⟨g, gi, ok⟩
  rw [e] at h
  change strictB g (fun g => bAnd(ok, bAnd(inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP g,
    allN 5 fun l => Nat.beq (pcomp 1782 11 (mask 11) g (nthN F.D l))
      (ePg 1782 11 F.D (nthN (nthL F.M i) l) g)))) = true at h
  rw [Orb.strictB_eq, bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨g, h.2.1, fun l hl => Nat.eq_of_beq_eq_true (allN_iff.1 h.2.2 l hl)⟩

theorem conj_φK {Q : Equiv.Perm (Fin 1782)} {M : List ℕ}
    (hQ : ∀ l : Fin 5, Q * dPerm l = φK (Multiplicative.ofAdd (vec (nthN M l))) * Q) (k : ℕ) :
    Q * φK (Multiplicative.ofAdd (vec k)) =
      φK (Multiplicative.ofAdd (vec (act5 M k))) * Q := by
  have hc : ∀ l : Fin 5, MulAut.conj Q (dPerm l) = φK (Multiplicative.ofAdd (vec (nthN M l))) := by
    intro l
    rw [MulAut.conj_apply, hQ l, mul_inv_cancel_right]
  have h1 : MulAut.conj Q (φK (Multiplicative.ofAdd (vec k))) =
      φK (Multiplicative.ofAdd (vec (act5 M k))) := by
    rw [φK_vec, vec_act5]
    simp only [map_mul, map_pow, ofAdd_add, ofAdd_nsmul]
    rw [hc 0, hc 1, hc 2, hc 3, hc 4]
    rfl
  rw [MulAut.conj_apply] at h1
  rw [← h1, inv_mul_cancel_right]

@[expose] def Good (m : ℕ) : Prop :=
  ∀ c ∈ suzM, (∀ k < 243, dot5 m k = 0 →
    c * φK (Multiplicative.ofAdd (vec k)) = φK (Multiplicative.ofAdd (vec k)) * c) → c ∈ DK

theorem good_child {p m g : ℕ}
    (hg : g < 2) (hp : Good p) (hmap : mapsTo (nthL F.M g) p m = true) : Good m := by
  obtain ⟨q, hq, hql⟩ := n_parts hg
  obtain ⟨hqp, hqm⟩ := mem_of_inPK hq
  set Q := permOfArr 1782 (unpack 1782 11 q) with hQdef
  have hQ0 := prep_of_permB13637 hqp
  have hQ : ∀ l : Fin 5, Q * dPerm l = φK (Multiplicative.ofAdd (vec (nthN (nthL F.M g) l))) * Q := by
    intro l
    have h1 := prep_pcomp n32_13637 hQ0 (prep_d l.2)
    rw [hql l l.2] at h1
    exact prep_eq13637 h1 (prep_ePg hQ0 _)
  have hconj := conj_φK hQ
  intro c hc hcm
  have hc' : Q⁻¹ * c * Q ∈ suzM := suzM.mul_mem (suzM.mul_mem (suzM.inv_mem hqm) hc) hqm
  have hD := hp _ hc' fun k hk hpk => by
    have hm := allN_iff.1 hmap k hk
    have hpk' : Nat.beq (dot5 p k) 0 = true := by rw [hpk]; rfl
    have hm' : Nat.beq (dot5 m (act5 (nthL F.M g) k)) 0 = true := by
      have : bIf(Nat.beq (dot5 p k) 0, Nat.beq (dot5 m (act5 (nthL F.M g) k)) 0, true) = true := hm
      rw [hpk'] at this
      exact this
    have e := hcm _ (act5_lt _ k) (Nat.eq_of_beq_eq_true hm')
    have hk2 := hconj k
    calc Q⁻¹ * c * Q * φK (Multiplicative.ofAdd (vec k))
        = Q⁻¹ * (c * (Q * φK (Multiplicative.ofAdd (vec k)))) := by group
      _ = Q⁻¹ * (c * φK (Multiplicative.ofAdd (vec (act5 (nthL F.M g) k))) * Q) := by
          rw [hk2, mul_assoc]
      _ = Q⁻¹ * (φK (Multiplicative.ofAdd (vec (act5 (nthL F.M g) k))) * c * Q) := by rw [e]
      _ = Q⁻¹ * (Q * φK (Multiplicative.ofAdd (vec k)) * Q⁻¹ * c * Q) := by rw [hk2]; group
      _ = φK (Multiplicative.ofAdd (vec k)) * (Q⁻¹ * c * Q) := by group
  obtain ⟨k, hk, hk'⟩ := DK_eq hD
  have : c = Q * φK (Multiplicative.ofAdd (vec k)) * Q⁻¹ := by
    rw [← hk']
    group
  rw [this, hconj k, mul_inv_cancel_right]
  exact mem_DK _

theorem nthN_append_lt13637 : ∀ (a b : List ℕ) (l : ℕ), l < a.length →
    nthN (List.append a b) l = nthN a l
  | _ :: _, _, 0, _ => rfl
  | _ :: a, b, l + 1, h => nthN_append_lt13637 a b l (by simp at h; omega)

theorem nthN_append_add13637 : ∀ (a b : List ℕ) (i : ℕ),
    nthN (List.append a b) (a.length + i) = nthN b i
  | [], b, i => by simp [List.append]
  | _ :: a, b, i => by
    rw [List.length_cons, show a.length + 1 + i = (a.length + i) + 1 by omega]
    exact nthN_append_add13637 a b i

theorem exists_nthN13637 : ∀ (b : List ℕ) (P : ℕ), P ∈ b → ∃ i < b.length, nthN b i = P
  | x :: b, P, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨i, hi, e⟩ := exists_nthN13637 b P h
      exact ⟨i + 1, by simp; omega, e⟩

theorem chB (r : ℕ) (hr : r < 17) : ch13637B r = true := by
  interval_cases r
  exacts [ch13637B0, ch13637B1, ch13637B2, ch13637B3, ch13637B4, ch13637B5, ch13637B6,
    ch13637B7, ch13637B8, ch13637B9, ch13637B10, ch13637B11, ch13637B12, ch13637B13,
    ch13637B14, ch13637B15, ch13637B16]

theorem chS (r : ℕ) (hr : r < 17) : ch13637S r = true := by
  interval_cases r
  exacts [ch13637S0, ch13637S1, ch13637S2, ch13637S3, ch13637S4, ch13637S5, ch13637S6,
    ch13637S7, ch13637S8, ch13637S9, ch13637S10, ch13637S11, ch13637S12, ch13637S13,
    ch13637S14, ch13637S15, ch13637S16]

theorem bind_parts {r : ℕ} (hr : r < 17) : ∃ g : ℕ,
    inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP g = true ∧
    ∀ t < 10, permB 1782 11 (nthN (List.append (nthL F.Yl r) (nthL F.Yp r)) t) = true ∧
      pcomp 1782 11 (mask 11) g (nthN (List.append (nthL F.Yl r) (nthL F.Yp r)) t) =
        ePg 1782 11 F.D (nthN (nthL F.ks r) t) g := by
  have h := chB r hr
  unfold ch13637B bindOK withReb at h
  rcases e : rebK 1782 11 SuzC.LR SuzC.TR SuzC.TRI (fun l => nthN (nthL F.gb r) l) 6 with
    ⟨g, gi, ok⟩
  rw [e] at h
  change strictB g (fun g => bAnd(ok, bAnd(inPK 1782 11 SuzC.LR SuzC.TRI SuzC.BP g,
    allN 10 fun t => strictB (nthN (List.append (nthL F.Yl r) (nthL F.Yp r)) t) fun Y =>
      bAnd(permB 1782 11 Y, Nat.beq (pcomp 1782 11 (mask 11) g Y)
        (ePg 1782 11 F.D (nthN (nthL F.ks r) t) g))))) = true at h
  rw [Orb.strictB_eq, bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨g, h.2.1, fun t ht => ?_⟩
  have h2 := allN_iff.1 h.2.2 t ht
  rw [Orb.strictB_eq, bAnd_eqS, Bool.and_eq_true] at h2
  exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem orth_parts {r : ℕ} (hr : r < 17) : ∀ t < 10,
    nthN (nthL F.ks r) t < 243 ∧ dot5 (nthN F.hm r) (nthN (nthL F.ks r) t) = 0 := by
  have h0 := orth_ok
  have h := allN_iff.1 h0 r hr
  unfold orthOK at h
  rw [bAnd_eqS, Bool.and_eq_true] at h
  intro t ht
  have h2 := allN_iff.1 h.2 t ht
  rw [bAnd_eqS, Bool.and_eq_true, Nat.blt_eq] at h2
  exact ⟨h2.1, Nat.eq_of_beq_eq_true h2.2⟩

theorem len_parts {r : ℕ} (hr : r < 17) :
    (nthL F.Yl r).length = 6 ∧ (nthL F.Yp r).length = 4 := by
  have h0 := len_ok
  unfold lenOK at h0
  have h := allN_iff.1 h0 r hr
  rw [bAnd_eqS, Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem good_root {r : ℕ}
    (hr : r < 17) : Good (nthN F.hm r) := by
  obtain ⟨g, hg, hY⟩ := bind_parts hr
  obtain ⟨hgp, hgm⟩ := mem_of_inPK hg
  obtain ⟨hl6, hl4⟩ := len_parts hr
  set G := permOfArr 1782 (unpack 1782 11 g) with hGdef
  have hG := prep_of_permB13637 hgp
  set Ys := List.append (nthL F.Yl r) (nthL F.Yp r) with hYs
  set m := nthN F.hm r with hm
  have hYt : ∀ t < 10, PRep 1782 11 (nthN Ys t)
      (G⁻¹ * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) * G) := by
    intro t ht
    have hP := prep_of_permB13637 (hY t ht).1
    have h1 := prep_pcomp n32_13637 hG hP
    rw [(hY t ht).2] at h1
    have e := prep_eq13637 h1 (prep_ePg hG _)
    have e' : permOfArr 1782 (unpack 1782 11 (nthN Ys t)) =
        G⁻¹ * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) * G := by
      rw [mul_assoc, ← e, inv_mul_cancel_left]
    rw [← e']
    exact hP
  intro c hc hcm
  set C : Subgroup (Equiv.Perm (Fin 1782)) :=
    Subgroup.centralizer {x | ∃ k < 243, dot5 m k = 0 ∧ x = φK (Multiplicative.ofAdd (vec k))} ⊓
      suzM with hCdef
  have hcomm : ∀ x ∈ C, ∀ t < 10, x * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) =
      φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) * x := by
    intro x hx t ht
    have := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).1) _
      ⟨_, (orth_parts hr t ht).1, (orth_parts hr t ht).2, rfl⟩
    exact this.symm
  set K := C.map (MulAut.conj G⁻¹).toMonoidHom with hK
  have hmemK : ∀ x ∈ K, ∃ y ∈ C, x = G⁻¹ * y * G := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact ⟨y, hy, by simp⟩
  have hKc : ∀ x ∈ K, ∀ t < 10, x * (G⁻¹ * φK (Multiplicative.ofAdd
      (vec (nthN (nthL F.ks r) t))) * G) =
      (G⁻¹ * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) * G) * x := by
    intro x hx t ht
    obtain ⟨y, hy, rfl⟩ := hmemK x hx
    have e := hcomm y hy t ht
    calc G⁻¹ * y * G * (G⁻¹ * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) * G)
        = G⁻¹ * (y * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t)))) * G := by group
      _ = G⁻¹ * (φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) t))) * y) * G := by rw [e]
      _ = _ := by group
  have hcard : Nat.card K ≤ 243 := by
    refine card_le_of_searchOK smallChain_arrays
      (CFSG.Certificates.chainCheckFacts smallChain_check.1) smallChain_valid Suz2306.binds
      Suz2306.perm SuzC.hl (chS r hr)
      (Y := fun l => G⁻¹ * φK (Multiplicative.ofAdd (vec (nthN (nthL F.ks r) l))) * G)
      (fun l hl => ?_) ?_ (fun x hx l hl => hKc x hx l (by omega)) ?_
    · rw [← nthN_append_lt13637 _ (nthL F.Yp r) l (by omega)]
      exact hYt l (by omega)
    · rw [smallChain_originalSubgroup]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hmemK x hx
      exact suzM.mul_mem (suzM.mul_mem (suzM.inv_mem hgm) (Subgroup.mem_inf.1 hy).2) hgm
    · intro P hP
      obtain ⟨i, hi, rfl⟩ := exists_nthN13637 _ P hP
      rw [hl4] at hi
      refine ⟨_, ?_, fun x hx => hKc x hx (6 + i) (by omega)⟩
      rw [← nthN_append_add13637 (nthL F.Yl r), hl6]
      exact hYt (6 + i) (by omega)
  have hcardC : Nat.card C ≤ 243 := by
    rwa [hK, Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective] at hcard
  have hDC : DK ≤ C := fun x hx => Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
    fun y ⟨k, _, _, hy⟩ => by rw [hy]; exact DK_comm _ (mem_DK k) x hx, DK_le hx⟩
  have hCD : C = DK := (Subgroup.eq_of_le_of_card_ge hDC (by rw [card_DK]; exact hcardC)).symm
  have hcC : c ∈ C := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2
    fun y ⟨k, hk, hmk, hy⟩ => by rw [hy]; exact (hcm k hk hmk).symm, hc⟩
  rw [← hCD]
  exact hcC

theorem memN_spec : ∀ (l : List ℕ) (x : ℕ), memN l x = true → ∃ r < l.length, nthN l r = x
  | a :: l, x, h => by
    cases hb : Nat.beq a x
    · have h' : memN l x = true := by
        have : bIf(Nat.beq a x, true, memN l x) = true := h
        rw [hb] at this
        exact this
      obtain ⟨r, hr, e⟩ := memN_spec l x h'
      exact ⟨r + 1, by simp; omega, e⟩
    · exact ⟨0, by simp, Nat.eq_of_beq_eq_true hb⟩

theorem memN_cons {a x : ℕ} {l : List ℕ} (h : memN (a :: l) x = true) : a = x ∨ memN l x = true := by
  cases hb : Nat.beq a x
  · right
    have : bIf(Nat.beq a x, true, memN l x) = true := h
    rw [hb] at this
    exact this
  · exact Or.inl (Nat.eq_of_beq_eq_true hb)

theorem hm_length : F.hm.length = 17 := by decide +kernel

theorem good_rows :
    ∀ (fr : List (List ℕ)) (seen : List ℕ), (∀ x, memN seen x = true → Good x) →
      rowsOK F.hm F.M fr seen = true → ∀ row ∈ fr, Good (nthN row 0)
  | [], _, _, _ => by simp
  | row :: fr, seen, hs, h => by
    have h' : bAnd(rowOK F.hm F.M seen row, rowsOK F.hm F.M fr (nthN row 0 :: seen)) = true := h
    rw [bAnd_eqS, Bool.and_eq_true] at h'
    obtain ⟨hrow, hrest⟩ := h'
    have hgood : Good (nthN row 0) := by
      unfold rowOK at hrow
      rw [bAnd_eqS, Bool.and_eq_true] at hrow
      obtain ⟨-, hb⟩ := hrow
      cases hg : Nat.beq (nthN row 2) 2
      · have hb' : bAnd(Nat.blt (nthN row 2) 2, bAnd(memN seen (nthN row 1),
            mapsTo (nthL F.M (nthN row 2)) (nthN row 1) (nthN row 0))) = true := by
          have : bIf(Nat.beq (nthN row 2) 2, bAnd(Nat.beq (nthN row 1) (nthN row 0),
              memN F.hm (nthN row 0)), bAnd(Nat.blt (nthN row 2) 2, bAnd(memN seen (nthN row 1),
                mapsTo (nthL F.M (nthN row 2)) (nthN row 1) (nthN row 0)))) = true := hb
          rw [hg] at this
          exact this
        rw [bAnd_eqS, bAnd_eqS, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq] at hb'
        exact good_child hb'.1 (hs _ hb'.2.1) hb'.2.2
      · have hb' : bAnd(Nat.beq (nthN row 1) (nthN row 0), memN F.hm (nthN row 0)) = true := by
          have : bIf(Nat.beq (nthN row 2) 2, bAnd(Nat.beq (nthN row 1) (nthN row 0),
              memN F.hm (nthN row 0)), bAnd(Nat.blt (nthN row 2) 2, bAnd(memN seen (nthN row 1),
                mapsTo (nthL F.M (nthN row 2)) (nthN row 1) (nthN row 0)))) = true := hb
          rw [hg] at this
          exact this
        rw [bAnd_eqS, Bool.and_eq_true] at hb'
        obtain ⟨r, hr, e⟩ := memN_spec _ _ hb'.2
        rw [hm_length] at hr
        rw [← e]
        exact good_root hr
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hgood
    · refine good_rows fr (nthN row 0 :: seen) (fun y hy => ?_) hrest x hx
      rcases memN_cons hy with rfl | hy
      · exact hgood
      · exact hs y hy

theorem memR_spec : ∀ (fr : List (List ℕ)) (x : ℕ), memR fr x = true →
    ∃ row ∈ fr, nthN row 0 = x
  | a :: fr, x, h => by
    cases hb : Nat.beq (nthN a 0) x
    · have h' : memR fr x = true := by
        have : bIf(Nat.beq (nthN a 0) x, true, memR fr x) = true := h
        rw [hb] at this
        exact this
      obtain ⟨row, hrow, e⟩ := memR_spec fr x h'
      exact ⟨row, List.mem_cons_of_mem _ hrow, e⟩
    · exact ⟨a, List.mem_cons_self, Nat.eq_of_beq_eq_true hb⟩

theorem centralizer_hyp
    {B : Subgroup (Equiv.Perm (Fin 1782))} (hBD : B ≤ DK) (hB : Nat.card B * 3 = 243) :
    Subgroup.centralizer (B : Set (Equiv.Perm (Fin 1782))) ⊓ suzM = DK := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨f, hf0, hf⟩ := Co3T.exists_dot_eq_zero_imp_mem φK φK_injective hBD
    (by rw [hB]; norm_num)
  have hx0 : idx f ≠ 0 := fun h => hf0 ((idx_eq_zero_iff f).1 h)
  have hfr := fr_ok
  unfold frOK at hfr
  rw [bAnd_eqS, Bool.and_eq_true] at hfr
  have hcov := allN_iff.1 hfr.2 (idx f) (idx_lt f)
  have hcov' : memR F.fr (canon5 (idx f)) = true := by
    have : bIf(Nat.beq (idx f) 0, true, memR F.fr (canon5 (idx f))) = true := hcov
    cases hb : Nat.beq (idx f) 0
    · rw [hb] at this
      exact this
    · exact absurd (Nat.eq_of_beq_eq_true hb) hx0
  obtain ⟨row, hrow, e⟩ := memR_spec _ _ hcov'
  have hgood := good_rows F.fr [] (fun x hx => absurd hx (by simp [memN])) hfr.1 row hrow
  rw [e] at hgood
  have hDC : DK ≤ Subgroup.centralizer (B : Set (Equiv.Perm (Fin 1782))) ⊓ suzM :=
    fun x hx => Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun b hb =>
      DK_comm b (hBD hb) x hx, DK_le hx⟩
  refine le_antisymm (fun c hc => hgood c (Subgroup.mem_inf.1 hc).2 fun k hk hdk => ?_) hDC
  have hs := dot5_canon hdk
  rw [vec_idx] at hs
  exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).1) _ (hf _ hs)).symm

end CFSG.KD.SuzThree13637

end
