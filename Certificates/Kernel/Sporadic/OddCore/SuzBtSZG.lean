module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtZG
public import Certificates.Kernel.Sporadic.OddCore.SuzBtSZF
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.HeFixKFix
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtSZG

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
open CFSG.Sporadic.SuzRecog.SuzL34Cert CertificateChecks.KernelSpor.SuzC1EG
open CertificateChecks.KernelSpor.SuzBtG CertificateChecks.KernelSpor.SuzBtZG

theorem kBT : Nat.beq (SuzBtT1.G 0) (SuzInvT1.F 0) = true := by quickRfl

@[expose] noncomputable def sgp (j : Nat) : Equiv.Perm (Fin 1782) :=
  decPerm (s1pDecs.getD j ([], 0))

@[expose] noncomputable def tgp (_ : Nat) : Equiv.Perm (Fin 1782) := suzInv 1

theorem hbT : ∀ t : Fin 3, pg 11 (mask 11) SuzBtT1.B t = c1Base t := by
  intro t
  fin_cases t <;> rfl

theorem hpT : ∀ i < SuzBtT1.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 1 SuzBtT1.cnt SuzBtT1.B
    SuzBtT1.G SuzBtT1.K SuzBtT1.R SuzBtT1.POS i = true := fun i hi =>
  btSl_spec SuzBtSZF.kT1Sl (Nat.zero_le _) (by rw [SuzBtSZF.kT1Cnt] at hi; omega) hi

theorem hpS : ∀ i < SuzBtS1.cnt, btPtK 1782 11 (mask 11) 3 33 (mask 33) 4 SuzBtS1.cnt SuzBtS1.B
    SuzBtS1.G SuzBtS1.K SuzBtS1.R SuzBtS1.POS i = true := by
  intro i hi
  have hi' := hi
  rw [SuzBtSF.kCnt] at hi'
  rcases Nat.lt_or_ge i 4096 with h1 | h1
  · rcases Nat.lt_or_ge i 2048 with h2 | h2
    · rcases Nat.lt_or_ge i 1024 with h3 | h3
      · exact btSl_spec SuzBtSF.kSl0 (by omega) (by omega) hi
      · exact btSl_spec SuzBtSF.kSl1 (by omega) (by omega) hi
    · rcases Nat.lt_or_ge i 3072 with h3 | h3
      · exact btSl_spec SuzBtSF.kSl2 (by omega) (by omega) hi
      · exact btSl_spec SuzBtSF.kSl3 (by omega) (by omega) hi
  · rcases Nat.lt_or_ge i 6144 with h2 | h2
    · rcases Nat.lt_or_ge i 5120 with h3 | h3
      · exact btSl_spec SuzBtSF.kSl4 (by omega) (by omega) hi
      · exact btSl_spec SuzBtSF.kSl5 (by omega) (by omega) hi
    · rcases Nat.lt_or_ge i 7168 with h3 | h3
      · exact btSl_spec SuzBtSF.kSl6 (by omega) (by omega) hi
      · exact btSl_spec SuzBtSF.kSl7 (by omega) (by omega) hi

theorem half {i : Nat} (hi : i < SuzBtS1.cnt) : i < 4096 ∨ (4096 ≤ i ∧ i < 4096 + 4096) := by
  rw [SuzBtSF.kCnt] at hi
  omega

theorem hgT : ∀ j < 1, ∀ x : Fin 1782, pg 11 (mask 11) (SuzBtT1.G j) x = tgp j x := by
  intro j hj x
  obtain rfl : j = 0 := by omega
  rw [Nat.eq_of_beq_eq_true kBT, ← CFSG.KC.HeFixK.unpack_getElem! x.2, ← SuzC1BF.pt1.1]
  exact CFSG.ComponentClassification.AS81.SuzB0.rep_tTab x

theorem t1_inv : suzInv 1 ∈ invE 1 := CFSG.ComponentClassification.AS81.SuzB0.suzInv_mem_invE

theorem s1_le : genSub 1782 4 sgp ≤ invE 1 := by
  rw [show genSub 1782 4 sgp = decSubgroup s1pDecs from genSub_dec s1pDecs]
  exact decSubgroup_le_invE (by decide)

theorem t1_le : genSub 1782 1 tgp ≤ invE 1 := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, -, rfl⟩
  exact t1_inv

theorem t1_mem : suzInv 1 ∈ genSub 1782 4 sgp := by
  have h := SuzBtSZF.kZT
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact mem_of_btKey s1_le hgS hbS hpS (Nat.blt_eq.mp h.1) t1_inv
    (mov_base hbS (hgT 0 (by norm_num)) h.2)

theorem m1_le_s1 : genSub 1782 8 mgp ≤ genSub 1782 4 sgp := by
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨j, hj, rfl⟩
  have h := CFSG.KS.Raw.Orb.allN_iff.1 SuzBtSZF.kLT j hj
  rw [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact mem_of_btKey s1_le hgS hbS hpS (Nat.blt_eq.mp h.1) (m1_le (gp_mem hj))
    (mov_base hbS (hgM j hj) h.2)

theorem hfixS : ∀ h ∈ genSub 1782 4 sgp, (∀ t, h (c1Base t) = c1Base t) → h = 1 :=
  fun h hh hfix => invE1_eq_one (s1_le hh) hfix

theorem t1_sq : suzInv 1 * suzInv 1 = 1 := suzInv_sq (by norm_num)

theorem mem_t1 {x : Equiv.Perm (Fin 1782)} (hx : x ∈ genSub 1782 1 tgp) :
    x = 1 ∨ x = suzInv 1 := by
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, -, rfl⟩ := ha
    exact Or.inr rfl
  | one => exact Or.inl rfl
  | mul a b _ _ ha hb =>
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl t1_sq
  | inv a _ ha =>
    rcases ha with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right t1_sq)

theorem center_iff {x : Equiv.Perm (Fin 1782)} (hx : x ∈ genSub 1782 4 sgp) :
    (∀ y ∈ genSub 1782 4 sgp, x * y = y * x) ↔ x = 1 ∨ x = suzInv 1 := by
  constructor
  · intro hc
    obtain ⟨q, hq, he⟩ := btCz_mem (m := 4) (Y := SuzBtS1.G) (y := sgp) (S := SuzBtS1Z.S)
      (RT := SuzBtS1Z.RT) hgS hpS hfixS hbS
      (fun j hj => mov_base hbS (hgS j hj) (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtSZF.kZS j hj))
      (fun i hi => (half hi).elim
        (fun h => btRtSl_spec SuzBtSZF.kZRt0 (Nat.zero_le _) (by omega) hi)
        (fun h => btRtSl_spec SuzBtSZF.kZRt1 h.1 h.2 hi))
      hgS (fun i hi => (half hi).elim
        (fun h => btCzSl_spec SuzBtSZF.kZCz0 (Nat.zero_le _) (by omega) hi)
        (fun h => btCzSl_spec SuzBtSZF.kZCz1 h.1 h.2 hi))
      SuzBtSF.kHd hx fun j hj => hc _ (gp_mem hj)
    exact mem_t1 (mem_of_btKey t1_le hgT hbT hpT hq (s1_le hx) he)
  · rintro (rfl | rfl) y hy
    · rw [one_mul, mul_one]
    · have h := s1_le hy
      rw [invE_eq_centM (by norm_num : 1 < 4)] at h
      exact (Subgroup.mem_centralizer_singleton_iff.1 h.1).symm

theorem cent_inf_eq : Subgroup.centralizer (genSub 1782 4 lgp : Set (Equiv.Perm (Fin 1782))) ⊓
    genSub 1782 4 sgp = genSub 1782 8 mgp := by
  apply le_antisymm
  · rintro x ⟨hc, hx⟩
    obtain ⟨q, hq, he⟩ := btCz_mem (m := 4) (Y := SuzBtL1.G) (y := lgp) (S := SuzBtS1L.S)
      (RT := SuzBtS1L.RT) hgS hpS hfixS hbS
      (fun j hj => mov_base hbS (hgL j hj) (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtSZF.kLS j hj))
      (fun i hi => (half hi).elim
        (fun h => btRtSl_spec SuzBtSZF.kLRt0 (Nat.zero_le _) (by omega) hi)
        (fun h => btRtSl_spec SuzBtSZF.kLRt1 h.1 h.2 hi))
      hgL (fun i hi => (half hi).elim
        (fun h => btCzSl_spec SuzBtSZF.kLCz0 (Nat.zero_le _) (by omega) hi)
        (fun h => btCzSl_spec SuzBtSZF.kLCz1 h.1 h.2 hi))
      SuzBtSF.kHd hx fun j hj => (Subgroup.mem_centralizer_iff.1 hc _ (gp_mem hj)).symm
    exact mem_of_btKey m1_le hgM hbM hpM hq (s1_le hx) he
  · intro x hx
    refine Subgroup.mem_inf.2 ⟨?_, m1_le_s1 hx⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.1 (l1_le_cent hl) x hx).symm

theorem l1_comm {i j : Nat} (hi : i < 4) (hj : j < 4) : lgp i * lgp j = lgp j * lgp i := by
  refine invE1_ext (Subgroup.mul_mem _ (l1_le (gp_mem hi)) (l1_le (gp_mem hj)))
    (Subgroup.mul_mem _ (l1_le (gp_mem hj)) (l1_le (gp_mem hi))) fun t => Fin.ext ?_
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1
    (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtZF.kL1C i hi) j hj) t t.2)
  rw [hbL t, hgL j hj, hgL i hi, hgL i hi, hgL j hj] at h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  exact h

theorem l1_sq {i : Nat} (hi : i < 4) : lgp i * lgp i = 1 := by
  refine invE1_ext (Subgroup.mul_mem _ (l1_le (gp_mem hi)) (l1_le (gp_mem hi))) (one_mem _)
    fun t => Fin.ext ?_
  have h := Nat.beq_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1
    (CFSG.KS.Raw.Orb.allN_iff.1 SuzBtZF.kL1I i hi) t t.2)
  rw [hbL t, hgL i hi, hgL i hi] at h
  rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  exact h

theorem l1_elemAb : CFSG.Open.IsElemAbelian 2 (genSub 1782 4 lgp) := by
  have hcomm : ∀ a ∈ {g | ∃ j < 4, lgp j = g}, ∀ b ∈ {g | ∃ j < 4, lgp j = g}, a * b = b * a := by
    rintro a ⟨i, hi, rfl⟩ b ⟨j, hj, rfl⟩
    exact l1_comm hi hj
  have hC : IsMulCommutative (genSub 1782 4 lgp) := CFSG.subgroup_isMulCommutative_closure hcomm
  refine ⟨hC, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨i, hi, rfl⟩ := ha
    rw [pow_two]
    exact l1_sq hi
  | one => exact one_pow 2
  | mul a b ha hb ha2 hb2 =>
    have hab : Commute a b := isMulCommutative_iff_of_setLike.mp hC a ha b hb
    rw [hab.mul_pow, ha2, hb2, one_mul]
  | inv a _ ha2 => rw [inv_pow, ha2, inv_one]

theorem card_L1 : Nat.card (genSub 1782 4 lgp) = 16 := by
  rw [← SuzBtZF.kL1Cnt]
  exact card_genSub_of_btK (w := 11) (kw := 33) (km := mask 33) (K := SuzBtL1.K)
    (R := SuzBtL1.R) (POS := SuzBtL1.POS) (by norm_num) l1_le hgL hbL SuzBtZF.kL1Hd hpL

theorem f1Prop_of_cls (hcls : ∀ e : Equiv.Perm (Fin 1782), e ∈ decSubgroup s1pDecs → e * e = 1 →
    e ≠ 1 → e ∉ decSubgroup l1Decs → 9 ≤ Nat.card ↥{x : Equiv.Perm (Fin 1782) |
      ∃ g ∈ decSubgroup s1pDecs, x = g * e * g⁻¹}) : F1Prop := by
  have eS : genSub 1782 4 sgp = decSubgroup s1pDecs := genSub_dec s1pDecs
  have eL : genSub 1782 4 lgp = decSubgroup l1Decs := genSub_dec l1Decs
  have eM : genSub 1782 8 mgp = decSubgroup m1Decs := genSub_dec m1Decs
  have hperm : permC 1782 CFSG.ComponentClassification.AS81.SuzB0.tTab = suzInv 1 := permC_tTab
  refine ⟨card_S1, ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, hcls⟩
  · rw [hperm, ← eS]
    exact t1_mem
  · rw [hperm]
    rw [← eS] at hx ⊢
    exact center_iff hx
  · rw [← eS, ← eL]
    exact l1_le_m1.trans m1_le_s1
  · rw [← eL]
    exact l1_elemAb
  · rw [← eL]
    exact card_L1
  · rw [← eS, ← eL, cent_inf_eq, eM]
    exact card_M1

end CertificateChecks.KernelSpor.SuzBtSZG

end
