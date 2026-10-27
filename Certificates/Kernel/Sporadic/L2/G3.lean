
module

public import Certificates.Kernel.Sporadic.L2.G2

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo
open CFSG.Sporadic.SuzRecog.LevelTwoData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pc" => pcomp 1782 11 (mask 11)

structure VtxOK : Prop where
  a : ∀ i < 2835, aChk i = true
  w : ∀ j < 162, wChk j = true
  sA : sortK 2835 fA ordA posA = true
  sT : sortK 486 fT ordT posT = true

variable (H : VtxOK)
include H

theorem hvA : ∀ i < 2835, aVt i = true := fun i hi => ((band _ _).1 (H.a i hi)).1

theorem hvW : ∀ j < 162, tVt j = true := fun j hj => ((band _ _).1 (H.w j hj)).1

theorem hvtA {s i : Nat} (hs : s < 2) (hi : i < 2835) : vtA s i = true := by
  have h := ((band _ _).1 (H.a i hi)).2
  rw [band] at h
  interval_cases s
  · exact h.1
  · exact h.2

theorem hvtW {s j : Nat} (hs : s < 2) (hj : j < 162) : vtW s j = true := by
  have h := ((band _ _).1 (H.w j hj)).2
  rw [band] at h
  interval_cases s
  · exact h.1
  · exact h.2

theorem sendsA {s v : Nat} (hs : s < 2) (hv : v < 2835) :
    sendsB gens[s]! gensInv[s]! v (vtab s)[v]! = true := by
  rw [vtab_getA (hvA H) H.sA hs hv (hvtA H hs hv),
    sendsB_eq (hvA H) (hvW H) (pG hs) (pGI hs) (by omega)]
  have h := hvtA H hs hv
  unfold vtA at h
  rw [sB, band, band, nblt, nbeq] at h
  obtain ⟨hlt, -, ht⟩ := h
  unfold sendsK
  rw [show Nat.blt v 2835 = true from nblt.2 hv, show Nat.blt (VK s v) 2835 = true from nblt.2 hlt]
  change Nat.beq (L2A (VK s v)) (pc (XG s) (pc (L2A v) (XGI s))) = true
  rcases hcb : bAnd(Nat.blt 0 (VK s v), bAnd(Nat.beq (aParK (VK s v)) v,
      Nat.beq (aLabK (VK s v)) s)) with _ | _
  · rw [hcb] at ht
    exact ht
  · rw [band, band, nblt, nbeq, nbeq] at hcb
    obtain ⟨h0, hp, hl⟩ := hcb
    obtain ⟨-, hstep, -, -⟩ := aVt_parts (hvA H _ hlt)
    obtain ⟨-, -, e⟩ := hstep h0
    rw [hp, hl] at e
    rw [e]
    exact Nat.beq_refl _

theorem aOK_true : aOK = true := by
  unfold aOK
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  refine ⟨⟨⟨aPts_size, ?_⟩, fun i hi => ⟨?_, ?_⟩⟩, fun s hs i hi => sendsA H hs hi⟩
  · rw [eqA_P (pA (hvA H) (by norm_num)) pT1]
    exact nbeq.2 ((aVt_parts (hvA H 0 (by norm_num))).1 rfl)
  · rw [(pA (hvA H) hi).1]
    exact (invEqK_sound (aVt_parts (hvA H i hi)).2.2.2).2
  · rw [fp_A (hvA H) hi]
    exact aIdx_get (hvA H) H.sA hi

theorem sendsW {s j : Nat} (hs : s < 2) (hj : j < 162) :
    sendsB gens[s]! gensInv[s]! (2835 + j) (vtab s)[2835 + j]! = true := by
  rw [vtab_getW (hvW H) H.sT hs hj (hvtW H hs hj),
    sendsB_eq (hvA H) (hvW H) (pG hs) (pGI hs) (by omega)]
  have h := hvtW H hs hj
  unfold vtW at h
  unfold sendsK
  rw [nblt_f (show ¬ 2835 + j < 2835 by omega),
    show Nat.sub (2835 + j) 2835 = j from Nat.add_sub_cancel_left 2835 j]
  simp only [show Nat.add 2835 j = 2835 + j from rfl] at h
  simp only [sB] at h ⊢
  exact h

theorem vOK_true : vOK = true := by
  unfold vOK
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff, Bool.not_eq_true']
  refine ⟨⟨⟨wPts_size, ?_⟩, fun j hj => ⟨⟨?_, ?_⟩, fun k hk => ?_⟩⟩, fun s hs j hj => sendsW H hs hj⟩
  · rw [eqA_P (pW (hvW H) (by norm_num)) pW0]
    exact nbeq.2 ((tVt_parts (hvW H 0 (by norm_num))).1 rfl)
  · rw [(pW (hvW H) hj).1]
    exact (invEqK_sound (tVt_parts (hvW H j hj)).2.2.2.2.2.1).2
  · rw [eqA_P (pT (hvW H) hj (by norm_num : 0 < 3)) (pT (hvW H) hj (by norm_num : 1 < 3))]
    exact Bool.eq_false_iff.2 fun e => (tVt_parts (hvW H j hj)).2.2.2.2.2.2 (nbeq.1 e)
  · rw [fp_T (hvW H) hj hk]
    exact vIdx_get (hvW H) H.sT hj hk

end CertificateChecks.KernelSpor.L2G

end
