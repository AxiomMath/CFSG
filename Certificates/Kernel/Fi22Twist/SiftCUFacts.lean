module

public import Certificates.Kernel.Fi22Twist.SiftCU
public import Certificates.Kernel.Fi22Twist.Q01Facts
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CertificateChecks.KernelFi22Rank.Q2 CFSG.KS.Raw
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

set_option maxRecDepth 400000

#kc_forall_tree su431009All (fun u => ch431009su u = true) 48 CFSG.KD.Fi22Twist.ch431009su

theorem sfCU_facts {u : ℕ} (hu : u < 48) : PP 3510 12 (sfCU u) ∧ Fi22X.cn (sfCU u) = true ∧
    Fi22X.siftP (sfCU u) = true := by
  have h := su431009All u hu
  unfold ch431009su at h
  rw [sB_eq] at h
  obtain ⟨hp, h2⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hc, hs⟩ := (bAnd_iff _ _).1 h2
  exact ⟨PP_of_permOK szA hp, hc, hs⟩

theorem sfCU_cg {r : ℕ} (hr : r < 23) : sfCU r = CG r := by
  have hb : Nat.blt r 23 = true := Eq.mpr Nat.blt_eq hr
  unfold sfCU
  rw [hb]

theorem sfCU_ug (r : ℕ) : sfCU (23 + r) = UG r := by
  have hb : Nat.blt (23 + r) 23 = false := Bool.eq_false_iff.2 fun h => by
    rw [Nat.blt_eq] at h
    omega
  unfold sfCU
  rw [hb]
  exact congrArg UG (Nat.add_sub_cancel_left 23 r)

theorem cg_PP {r : ℕ} (hr : r < 23) : PP 3510 12 (CG r) := by
  rw [← sfCU_cg hr]
  exact (sfCU_facts (by omega)).1

theorem ug_PP {r : ℕ} (hr : r < 25) : PP 3510 12 (UG r) := by
  rw [← sfCU_ug r]
  exact (sfCU_facts (by omega)).1


theorem cg_memP {r : ℕ} (hr : r < 23) : permOfArr 3510 (unpack 3510 12 (CG r)) ∈ fi22P := by
  obtain ⟨hP, hc, hs⟩ := sfCU_facts (u := r) (by omega)
  rw [sfCU_cg hr] at hP hc hs
  exact mem_P_of_PP hP hc hs

theorem ug_memP {r : ℕ} (hr : r < 25) : permOfArr 3510 (unpack 3510 12 (UG r)) ∈ fi22P := by
  obtain ⟨hP, hc, hs⟩ := sfCU_facts (u := 23 + r) (by omega)
  rw [sfCU_ug r] at hP hc hs
  exact mem_P_of_PP hP hc hs

end CertificateChecks.KernelFi22Twist

end
