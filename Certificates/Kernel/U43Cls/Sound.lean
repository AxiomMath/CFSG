module

public import Certificates.Kernel.U43Cls.Checks
public import Certificates.Kernel.U43Mod.Glue
public import CFSG.Certificates.Kernel.U43Cls.ConjSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Cls

open CFSG.KC.Enum CFSG.KC.U43Mod CFSG.KC.U43Cls CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb
  CFSG.KS.U43Mod CFSG.KS.U43Cls CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.EvenSporadicStandard.M24Std.CU43 CertificateChecks.KernelU43B CFSG.Quasithin.H13.U43
  CFSG.Sporadic.SmallOddCore CertificateChecks.KernelU43Mod

@[expose] noncomputable def EP (j : ℕ) : Equiv.Perm (Fin 820) :=
  permOfArr 820 (unpack 820 10 (ET j))

@[expose] noncomputable def gC (c : ℕ) : Equiv.Perm (Fin 820) :=
  if c = 0 then CP 0 else if c = 1 then CP 1 else if c = 2 then (CP 1)⁻¹ else EP (c - 3)

theorem kET_spec {j : ℕ} (hj : j < 16) :
    permOK 820 10 (mask 10) (820 * 10) (ET j) (ETI j) = true ∧ inPU (ET j) = true :=
  (bAnd_iff _ _).1 (allN_spec kET j hj)

theorem rep_EP {j : ℕ} (hj : j < 16) : Rep 820 (unpack 820 10 (ET j)) (EP j) :=
  (rep_permOfArr (isInvA_unpack (kET_spec hj).1)).1

theorem letRep_EP {j : ℕ} (hj : j < 16) :
    LetRep 820 (fun j q => pg 10 (mask 10) (ET j) q) (fun j q => pg 10 (mask 10) (ETI j) q) EP j := by
  have h := rep_permOfArr (isInvA_unpack (kET_spec hj).1)
  intro q hq
  refine ⟨?_, ?_⟩
  · change pg 10 (mask 10) (ET j) q = _
    rw [← unpack_get hq]
    exact h.1 ⟨q, hq⟩
  · change pg 10 (mask 10) (ETI j) q = _
    rw [← unpack_get hq]
    exact h.2 ⟨q, hq⟩

theorem EP_mem {j : ℕ} (hj : j < 16) : EP j ∈ P := by
  have hr : allN 820 (fun i => Nat.blt (pg 10 (mask 10) (ET j) i) 820) = true :=
    CFSG.KS.PackFld.allN_of_forall fun i hi => by
      rw [← unpack_get hi]
      exact Nat.blt_eq.mpr ((rep_EP hj).lt hi)
  have hs := siftK_sound binds perm C.hl rfl hr (kET_spec hj).2
  rw [← base_eq] at hs
  exact (inP_iff (rep_EP hj)).1 hs

theorem blt_three {c : ℕ} (hc : 3 ≤ c) : Nat.blt c 3 = false := by
  rw [Bool.eq_false_iff, Ne, Nat.blt_eq]
  omega

theorem GC_ge {c : ℕ} (hc : 3 ≤ c) (q : ℕ) : GC c q = pg 10 (mask 10) (ET (c - 3)) q := by
  unfold GC
  rw [blt_three hc]
  rfl

theorem GCi_ge {c : ℕ} (hc : 3 ≤ c) (q : ℕ) : GCi c q = pg 10 (mask 10) (ETI (c - 3)) q := by
  unfold GCi
  rw [blt_three hc]
  rfl

theorem gC_ge {c : ℕ} (hc : 3 ≤ c) : gC c = EP (c - 3) := by
  unfold gC
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem pair_GA {i : ℕ} (hi : i < 7) : PairRep 820 (GA i) (GAi i) (CP i) := letRep_GA hi

theorem letRep_GC {c : ℕ} (hc : c < 19) : LetRep 820 GC GCi gC c := by
  rcases Nat.lt_or_ge c 3 with h3 | h3
  · interval_cases c
    · have h : PairRep 820 (GC 0) (GCi 0) (CP 0) := pair_GA (by norm_num)
      have e : gC 0 = CP 0 := by simp [gC]
      rw [← e] at h
      exact h.letRep
    · have h : PairRep 820 (GC 1) (GCi 1) (CP 1) := pair_GA (by norm_num)
      have e : gC 1 = CP 1 := by simp [gC]
      rw [← e] at h
      exact h.letRep
    · have h : PairRep 820 (GC 2) (GCi 2) (CP 1)⁻¹ := (pair_GA (i := 1) (by norm_num)).inv
      have e : gC 2 = (CP 1)⁻¹ := by simp [gC]
      rw [← e] at h
      exact h.letRep
  · have h : PairRep 820 (fun q => pg 10 (mask 10) (ET (c - 3)) q)
        (fun q => pg 10 (mask 10) (ETI (c - 3)) q) (EP (c - 3)) := letRep_EP (by omega)
    have e1 : GC c = fun q => pg 10 (mask 10) (ET (c - 3)) q := funext (GC_ge h3)
    have e2 : GCi c = fun q => pg 10 (mask 10) (ETI (c - 3)) q := funext (GCi_ge h3)
    rw [← e1, ← e2, ← gC_ge h3] at h
    exact h.letRep

theorem gC_mem {c : ℕ} (hc : c < 19) : gC c ∈ P := by
  rcases Nat.lt_or_ge c 3 with h3 | h3
  · interval_cases c
    · simpa [gC] using CP_mem (i := 0) (by norm_num)
    · simpa [gC] using CP_mem (i := 1) (by norm_num)
    · simpa [gC] using P.inv_mem (CP_mem (i := 1) (by norm_num))
  · rw [gC_ge h3]
    exact EP_mem (by omega)

@[expose] noncomputable def xP : Equiv.Perm (Fin 820) := CP 1 * CP 0

@[expose] noncomputable def yv (s : ℕ) : Equiv.Perm (Fin 820) := if s = 0 then xP else xP * xP

theorem pair_X : PairRep 820 X Xi xP :=
  (pair_GA (i := 1) (by norm_num)).comp (pair_GA (i := 0) (by norm_num))

theorem letRep_Y {s : ℕ} (hs : s < 2) : LetRep 820 Y Yi yv s := by
  interval_cases s
  · have h : PairRep 820 (Y 0) (Yi 0) xP := pair_X
    have e : yv 0 = xP := by simp [yv]
    rw [← e] at h
    exact h.letRep
  · have h2 := pair_X.comp pair_X
    have h : PairRep 820 (Y 1) (Yi 1) (xP * xP) := by
      intro q hq
      change strictN (X q) X = _ ∧ strictN (Xi q) Xi = _
      rw [U43Mod.strictN_eq, U43Mod.strictN_eq]
      exact h2 q hq
    have e : yv 1 = xP * xP := by simp [yv]
    rw [← e] at h
    exact h.letRep

theorem kX_spec : baseEq bs (fpow X 7) (fun q => q) = true ∧ baseEq bs X (fun q => q) = false := by
  have h := kX
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact h

theorem xP_mem : xP ∈ P :=
  P.mul_mem (CP_mem (by norm_num)) (CP_mem (by norm_num))

theorem xP_pow : xP ^ 7 = 1 :=
  eq_of_baseEq (P.pow_mem xP_mem 7) P.one_mem (fpow_eq (fun q hq => (pair_X q hq).1) 7) id_eq'
    kX_spec.1

theorem xP_ne : xP ≠ 1 := ne_of_baseEq (fun q hq => (pair_X q hq).1) id_eq' kX_spec.2

@[expose] noncomputable def clsE (i : ℕ) : Equiv.Perm (Fin 820) := cjV gC (CP 0) (RT i)

theorem recC_all : ∀ c, 64 * c < 2835 →
    cBlk RT GC GCi (GA 0) Y Yi 19 0 1 9 2835 c = true := by
  intro c hc
  have hc' : c < 45 := by omega
  interval_cases c
  exacts [recC0, recC1, recC2, recC3, recC4, recC5, recC6, recC7, recC8, recC9, recC10, recC11,
    recC12, recC13, recC14, recC15, recC16, recC17, recC18, recC19, recC20, recC21, recC22, recC23,
    recC24, recC25, recC26, recC27, recC28, recC29, recC30, recC31, recC32, recC33, recC34, recC35,
    recC36, recC37, recC38, recC39, recC40, recC41, recC42, recC43, recC44]

theorem cls_sound :
    (∀ i < 2835, clsE i ∈ conjClass P (CP 0)) ∧
    (∀ i < 2835, ∀ i' < 2835, clsE i = clsE i' → i = i') ∧
    (∀ i < 2835, ∃ s < 2, clsE i * (yv s * clsE i * (yv s)⁻¹) ≠
      yv s * clsE i * (yv s)⁻¹ * clsE i) := by
  obtain ⟨h1, h2, h3⟩ := cRec_sound (N := 2835) (fun c hc => letRep_GC hc)
    (GA_eq (i := 0) (by norm_num)) (fun s hs => letRep_Y hs) (by norm_num) (by norm_num)
    (by norm_num) (cBlk_spec recC_all)
  refine ⟨fun i hi => ?_, h2, h3⟩
  obtain ⟨w, hw, e⟩ := h1 i hi P fun c hc => gC_mem hc
  exact ⟨w, hw, e⟩

end CertificateChecks.KernelU43Cls

end
