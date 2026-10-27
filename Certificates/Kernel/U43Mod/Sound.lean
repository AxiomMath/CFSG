module

public import Certificates.Kernel.U43Mod.Checks
public import Certificates.Kernel.Multipliers.U43BFacts
public import CFSG.Certificates.Kernel.U43Mod.KTreeSound
public import CFSG.Certificates.Kernel.Spor.BaseSep
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Chain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Mod

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.U43Mod
  CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43

theorem bs_lt : ∀ p ∈ bs, p < 820 := by decide

theorem eq_one_of_base {G : Equiv.Perm (Fin 820)} (hG : G ∈ P)
    (h : ∀ p (hp : p ∈ bs), G ⟨p, bs_lt p hp⟩ = ⟨p, bs_lt p hp⟩) : G = 1 := by
  have hv := validSchreier_of_chainOK chainArrays (by norm_num : 0 < 4)
    CFSG.LieType.Multipliers.U43.chain_check
  refine RawSchreierDatum.eq_one_of_fixes_base Q hv.1 hG fun i => ?_
  have hm : Q.base.get i ∈ Q.base.toList := by simp [Vector.get, Vector.toList]
  have hb : Q.base.toList = CFSG.LieType.Multipliers.U43.chainBase :=
    RawSchreierDatum.ofArrays_base_toList
  rw [hb] at hm
  simp only [CFSG.LieType.Multipliers.U43.chainBase, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  rcases hm with e | e | e <;> rw [e]
  · exact h 0 (by decide)
  · exact h 1 (by decide)
  · exact h 9 (by decide)

theorem eq_of_base {x y : Equiv.Perm (Fin 820)} (hx : x ∈ P)
    (hy : y ∈ P) (h : ∀ p (hp : p ∈ bs), x ⟨p, bs_lt p hp⟩ = y ⟨p, bs_lt p hp⟩) : x = y := by
  have h1 : y⁻¹ * x = 1 := eq_one_of_base (P.mul_mem (P.inv_mem hy) hx) fun p hp => by
    rw [Equiv.Perm.mul_apply, h p hp]
    simp
  rw [← mul_left_cancel_iff (a := y⁻¹), h1, inv_mul_cancel]

@[expose] noncomputable def CP (i : ℕ) : Equiv.Perm (Fin 820) :=
  permOfArr 820 (unpack 820 10 (C.S i))

theorem letRep_GA {i : ℕ} (hi : i < 7) : LetRep 820 GA GAi CP i := by
  have h := rep_permOfArr (isInvA_unpack (allN_spec perm i hi))
  intro q hq
  refine ⟨?_, ?_⟩
  · change pg 10 (mask 10) (C.S i) q = _
    rw [← unpack_get hq]
    exact h.1 ⟨q, hq⟩
  · change pg 10 (mask 10) (C.SI i) q = _
    rw [← unpack_get hq]
    exact h.2 ⟨q, hq⟩

theorem CP_zero : CP 0 = CFSG.LieType.Multipliers.U43.psi CFSG.LieType.Multipliers.U43.xElt := by
  have ha : CFSG.LieType.Multipliers.U43.chainS[0]! = unpack 820 10 (C.S 0) :=
    binds.2.2.2.2.1 0 (by omega)
  have hA : Rep 820 CFSG.LieType.Multipliers.U43.chainS[0]!
    (CFSG.LieType.Multipliers.U43.psi CFSG.LieType.Multipliers.U43.xElt) :=
    CFSG.LieType.Multipliers.U43.rep_tabA
  rw [ha] at hA
  exact (rep_permOfArr (isInvA_unpack (allN_spec perm 0 (by norm_num)))).1.unique hA

theorem CP_one : CP 1 = CFSG.LieType.Multipliers.U43.psi CFSG.LieType.Multipliers.U43.yElt := by
  have hb : CFSG.LieType.Multipliers.U43.chainS[1]! = unpack 820 10 (C.S 1) :=
    binds.2.2.2.2.1 1 (by omega)
  have hB : Rep 820 CFSG.LieType.Multipliers.U43.chainS[1]!
    (CFSG.LieType.Multipliers.U43.psi CFSG.LieType.Multipliers.U43.yElt) :=
    CFSG.LieType.Multipliers.U43.rep_tabB
  rw [hb] at hB
  exact (rep_permOfArr (isInvA_unpack (allN_spec perm 1 (by norm_num)))).1.unique hB

theorem gW_letters : ∀ i, ∀ l ∈ gW.getD i [], l.1 < 2 := by
  intro i
  rcases Nat.lt_or_ge i 5 with hi | hi
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simpa [gW] using hi)]
    simp

theorem letRep_GM (i : ℕ) : LetRep 820 GM GMi (fun i => evalG CP (gW.getD i [])) i :=
  letRep_wG fun l hl => letRep_GA (by have := gW_letters i l hl; omega)

@[expose] noncomputable def SP (j : ℕ) : Equiv.Perm (Fin 820) := permOfArr 820 (unpack 820 10 (ST j))

theorem kST_spec {j : ℕ} (hj : j < 3) :
    permOK 820 10 (mask 10) (820 * 10) (ST j) (STI j) = true ∧ inPU (ST j) = true ∧
      baseEq bs (GS j) (wG GM GMi sW j) = true := by
  have h := allN_spec kST j hj
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h2
  exact ⟨h1, h2, h3⟩

theorem rep_SP {j : ℕ} (hj : j < 3) : Rep 820 (unpack 820 10 (ST j)) (SP j) :=
  (rep_permOfArr (isInvA_unpack (kST_spec hj).1)).1

theorem GS_eq {j : ℕ} (hj : j < 3) (q : ℕ) (hq : q < 820) : GS j q = (SP j ⟨q, hq⟩ : ℕ) := by
  change pg 10 (mask 10) (ST j) q = _
  rw [← unpack_get hq]
  exact rep_SP hj ⟨q, hq⟩

theorem SP_mem {j : ℕ} (hj : j < 3) : SP j ∈ P := by
  have hr : allN 820 (fun i => Nat.blt (pg 10 (mask 10) (ST j) i) 820) = true :=
    CFSG.KS.PackFld.allN_of_forall fun i hi => by
      rw [← unpack_get hi]
      exact Nat.blt_eq.mpr ((rep_SP hj).lt hi)
  have hs := siftK_sound binds perm C.hl rfl hr (kST_spec hj).2.1
  rw [← base_eq] at hs
  exact (inP_iff (rep_SP hj)).1 hs

theorem card_Ssub :
    Nat.card (Subgroup.closure (SP '' Set.Iio 3)) = 128 := by
  have hle : Subgroup.closure (SP '' Set.Iio 3) ≤ P := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact SP_mem hj
  exact card_of_kTree (T := KT) (iw := 8) (im := 255) (G := GS) rfl bs_lt
    (fun j hj q hq => GS_eq hj q hq)
    (fun x hx y hy h => eq_of_base (hle hx) (hle hy) h) kKT

end CertificateChecks.KernelU43Mod

end
