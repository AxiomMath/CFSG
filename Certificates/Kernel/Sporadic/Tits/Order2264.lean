module

public import Certificates.Kernel.Sporadic.Tits.GroupT2264
public import CFSG.Certificates.Kernel.Spor.PresCardPG
public import CFSG.Certificates.Kernel.Spor.IndexTwo
public import CFSG.Certificates.Kernel.Spor.RawCard
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Tits2264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PresPG CFSG.KS.IndexTwo
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native CFSG.LieType.Multipliers.Tits CertificateChecks.KernelMisc

theorem chainP : rawChainOK 1755 (titsPerfectArrs.extract 0 2) titsPerfectArrs
    (baseArr 1755 titsPerfectBase) (wordsArr 2 12 titsPerfectDerivations) 4 = true := by
  refine rawChainK_of_card_orb 4 bindsP TitsP.head TitsP.ho (by norm_num) ?_
  rw [orbitsP]
  have hle : Subgroup.closure (Set.range fun j : Fin 2 => permOfArr 1755 titsPerfectArrs[j.val]!) ≤ T := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    change permOfArr 1755 titsPerfectArrs[j.val]! ∈ T
    rw [perf_eq (j := j.val) (by omega)]
    rcases j with ⟨_ | _ | j, hj⟩
    · exact mem_T (sift_spec 6 (by norm_num)).1 (sift_spec 6 (by norm_num)).2
    · exact mem_T (sift_spec 7 (by norm_num)).1 (sift_spec 7 (by norm_num)).2
    · omega
  exact (Subgroup.card_le_of_le hle).trans (card_T.trans (by norm_num))

@[expose] noncomputable def t : Equiv.Perm (Fin 1755) := permOfArr 1755 (unpack 1755 11 (G 1))

theorem perm_mul {P Q : Nat} (hP : permC P = true) (hQ : permC Q = true)
    (hPQ : permC (pcomp 1755 11 (mask 11) P Q) = true) :
    permOfArr 1755 (unpack 1755 11 (pcomp 1755 11 (mask 11) P Q)) =
      permOfArr 1755 (unpack 1755 11 P) * permOfArr 1755 (unpack 1755 11 Q) := by
  have r := rep_compA (rep_of hP).1 (rep_of hQ).1
  rw [compA_unpack (permC_spec hP).2.1 (permC_spec hQ).2.1] at r
  exact (rep_of hPQ).1.unique r

theorem permD_spec (j : Nat) (hj : j < 2) : permC (TitsD.S j) = true := by
  rw [← Nat.eq_of_beq_eq_true (allN_spec dOK j hj)]
  exact (w_spec hj).2.2.1

theorem gperm : ∀ k < 4, permC (G k) = true := fun k hk => allN_spec gOK k hk

theorem chainA : rawChainOK 1755 (titsAmbientArrs.extract 0 4) titsAmbientArrs
    (baseArr 1755 titsAmbientBase) (wordsArr 4 14 titsAmbientDerivations) 4 = true := by
  refine rawChainK_of_card_orb 4 bindsA TitsA.head TitsA.ho (by norm_num) ?_
  rw [orbitsA]
  have ambG : ∀ j < 4, titsAmbientArrs[j]! = unpack 1755 11 (G j) := by
    intro j hj
    rw [amb_eq (by omega)]
    interval_cases j
    · exact congrArg _ (Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (TitsA.S 0) (G 0) = true))
    · exact congrArg _ (Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (TitsA.S 1) (G 1) = true))
    · exact congrArg _ (Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (TitsA.S 2) (G 2) = true))
    · exact congrArg _ (Nat.eq_of_beq_eq_true (by quickRfl : Nat.beq (TitsA.S 3) (G 3) = true))
  have rt := rep_of (gperm 1 (by norm_num))
  have ht2 : t * t ∈ T := by
    have h := mem_T (sift_spec 3 (by norm_num)).1 (sift_spec 3 (by norm_num)).2
    change permOfArr 1755 (unpack 1755 11 (pcomp 1755 11 (mask 11) (G 1) (G 1))) ∈ T at h
    rwa [perm_mul (gperm 1 (by norm_num)) (gperm 1 (by norm_num)) (sift_spec 3 (by norm_num)).2] at h
  have hconj : ∀ h ∈ T, t * h * t⁻¹ ∈ T := by
    refine conj_mem_of_gens T t _ rfl ?_
    rintro _ ⟨j, rfl⟩
    have k4 : j.val + 4 < 8 := by omega
    have hs := sift_spec (j.val + 4) k4
    have e : toSift (j.val + 4) = tdt j.val := by
      rcases j with ⟨_ | _ | j, hj⟩
      · rfl
      · rfl
      · omega
    rw [e] at hs
    have h := mem_T hs.1 hs.2
    have rd := rep_of (permD_spec j.val j.2)
    have r := rep_compA rt.1 (rep_compA rd.1 rt.2)
    rw [compA_unpack (permC_spec (permD_spec j.val j.2)).2.1 (permC_spec (gperm 1 (by norm_num))).2.2,
      compA_unpack (permC_spec (gperm 1 (by norm_num))).2.1
        (canonK_pcomp (permC_spec (permD_spec j.val j.2)).2.1
          (permC_spec (gperm 1 (by norm_num))).2.2)] at r
    have e2 := (rep_of hs.2).1.unique r
    change permOfArr 1755 (unpack 1755 11 (tdt j.val)) ∈ T at h
    rw [e2] at h
    have ed : d j.val = permOfArr 1755 (unpack 1755 11 (TitsD.S j.val)) := by
      rw [d, der_eq (by omega)]
    change t * d j.val * t⁻¹ ∈ T
    rw [ed, mul_assoc]
    exact h
  have hS : ∀ s ∈ Set.range (fun j : Fin 4 => permOfArr 1755 titsAmbientArrs[j.val]!),
      s ∈ T ∨ s * t⁻¹ ∈ T := by
    rintro _ ⟨j, rfl⟩
    change permOfArr 1755 titsAmbientArrs[j.val]! ∈ T ∨ permOfArr 1755 titsAmbientArrs[j.val]! * t⁻¹ ∈ T
    rw [ambG j.val j.2]
    rcases j with ⟨_ | _ | _ | _ | j, hj⟩
    · exact Or.inl (mem_T (sift_spec 0 (by norm_num)).1 (sift_spec 0 (by norm_num)).2)
    · refine Or.inr ?_
      change t * t⁻¹ ∈ T
      rw [mul_inv_cancel]
      exact T.one_mem
    · exact Or.inl (mem_T (sift_spec 1 (by norm_num)).1 (sift_spec 1 (by norm_num)).2)
    · exact Or.inl (mem_T (sift_spec 2 (by norm_num)).1 (sift_spec 2 (by norm_num)).2)
    · omega
  have hT := card_T
  have hp : ([1755, 80, 8, 2, 4, 4] : List Nat).prod = 35942400 := by norm_num
  rw [hp]
  exact (card_closure_le_two_mul T t _ hS hconj ht2).trans (by omega)

end CertificateChecks.KernelSpor.Tits2264

end
