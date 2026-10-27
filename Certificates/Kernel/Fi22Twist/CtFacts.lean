module

public import Certificates.Kernel.Fi22Twist.CtChk
public import Certificates.Kernel.Fi22Twist.Q01Facts
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.Certificates.Kernel.Fi22Twist.CtSound
public import CFSG.Certificates.Kernel.SchreierFam.CqKSound
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CertificateChecks.KernelFi22Rank.Q2 CFSG.KS.Raw
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

set_option maxRecDepth 400000

#kc_forall_tree ct431009All (fun u => ch431009ct u = true) 11 CFSG.KD.Fi22Twist.ch431009ct

theorem tArr_prep {k : ℕ} (hk : k < 3) : PRep 3510 12 (MonoidHom.id _)
    (CertificateChecks.KernelSpor.Fi22ExtT.L (21 + k)) (permOfArr 3510 (tArr k)) := by
  have e : tArr k = unpack 3510 12 (CertificateChecks.KernelSpor.Fi22ExtT.L (21 + k)) :=
    CertificateChecks.KernelSpor.Fi22E2067.ext_eq (by omega)
  rw [e]
  exact prep_of_PP (CFSG.KS.SchreierFam.PP_of_permOK' szA
    (CertificateChecks.KernelSpor.Fi22E2067.perm3510 (by omega)))

theorem ct_comm {u k : ℕ} (hu : u < 11) (hk : ctI u = 21 + k) (hk3 : k < 3)
    (hP : PP 3510 12 (sfG (23 + u))) :
    permOfArr 3510 (tArr k) * permOfArr 3510 (unpack 3510 12 (sfG (23 + u))) =
      permOfArr 3510 (unpack 3510 12 (sfG (23 + u))) * permOfArr 3510 (tArr k) := by
  have h := ct431009All u hu
  unfold ch431009ct at h
  rw [hk] at h
  exact (ctK_comm (prep_of_PP hP) (tArr_prep hk3) h).symm

theorem qk_le_cent {k : ℕ} (hk : k < 3) : Subgroup.closure (permsA 3510 (qGens k)) ≤
    Subgroup.centralizer {permOfArr 3510 (tArr k)} := by
  have hc : ∀ {u : ℕ} {g : Equiv.Perm (Fin 3510)}, u < 11 → ctI u = 21 + k →
      PP 3510 12 (sfG (23 + u)) → permOfArr 3510 (unpack 3510 12 (sfG (23 + u))) = g →
      g ∈ Subgroup.centralizer {permOfArr 3510 (tArr k)} := by
    intro u g hu hi hP hg
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [← hg]
    exact ct_comm hu hi hk hP
  interval_cases k
  · obtain ⟨hPP, hset⟩ := q01_gens qGens0_eq ch431009q0x
    rw [hset, Subgroup.closure_le]
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    have e := sfG_q0 ht
    refine hc (u := t) (by omega) ?_ (by rw [e]; exact hPP t ht) (by rw [e])
    interval_cases t <;> rfl
  · obtain ⟨hPP, hset⟩ := q01_gens qGens1_eq ch431009q1x
    rw [hset, Subgroup.closure_le]
    rintro _ ⟨⟨t, ht⟩, rfl⟩
    have e : sfG (23 + (3 + t)) = KQ1 (Nat.succ t) := by
      rw [← Nat.add_assoc]
      exact sfG_q1 ht
    refine hc (u := 3 + t) (by omega) ?_ (by rw [e]; exact hPP t ht) (by rw [e])
    interval_cases t <;> rfl
  · obtain ⟨hsz, hget⟩ := CFSG.KC.Fi22RkS.rows_of (m := 3510) (K := 5) (w := 12) (by norm_num)
      szA rowsT
    rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i < 5 := by
      have h : i < (qGens 2).size := hi
      rwa [qGens_eq, hsz] at h
    have e : sfG (23 + (6 + i)) = key (GI i) := by
      rw [← Nat.add_assoc]
      exact sfG_q2 hi'
    refine hc (u := 6 + i) (by omega) ?_ (by rw [e]; exact (hget i hi').2) ?_
    · interval_cases i <;> rfl
    · beta_reduce
      rw [e, qGens_eq, (hget i hi').1]

end CertificateChecks.KernelFi22Twist

end
