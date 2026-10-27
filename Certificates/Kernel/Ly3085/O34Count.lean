
module

public import Certificates.Kernel.Ly3085.FiberCount
public import Certificates.Kernel.Ly3085.Omega.S3K0
public import Certificates.Kernel.Ly3085.Omega.S3K1
public import Certificates.Kernel.Ly3085.Omega.S3K2
public import Certificates.Kernel.Ly3085.Omega.S3K3
public import Certificates.Kernel.Ly3085.Omega.S3K4
public import Certificates.Kernel.Ly3085.Omega.S3K5
public import Certificates.Kernel.Ly3085.Omega.S3K6
public import Certificates.Kernel.Ly3085.Omega.SmallK
public import Certificates.Kernel.Ly3085.Omega.FibK
public import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.Ly3085.FiberGlue

public section

namespace CFSG.KD.LyS3

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b = true) 6358 CFSG.KD.LyS3.s3

#kc_forall_tree sortsOK (fun k => CFSG.KC.LyOm.sSort KX SG n (4096 * k) 4096 = true) 99
  CFSG.KD.LyS3.s3s

theorem n_eq : n = 406875 := by decide +kernel

theorem nl_eq : nl = 6358 := by decide +kernel

end CFSG.KD.LyS3

namespace CFSG.KD.LyS4

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b = true) 122 CFSG.KD.LyS4.s4

theorem n_eq : n = 7750 := by decide +kernel

end CFSG.KD.LyS4

namespace CFSG.KD.LyF3

theorem n_eq : n = 5 := by decide +kernel

theorem nc_eq : nc = 1 := by decide +kernel

end CFSG.KD.LyF3

namespace CFSG.KD.LyF4

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.cRange BC KX PT WT GT WC nc n b 1 = true) 12
  CFSG.KD.LyF4.f4

theorem n_eq : n = 750 := by decide +kernel

theorem nc_eq : nc = 1 := by decide +kernel

end CFSG.KD.LyF4

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open Matrix MulAction

theorem wf30_lt : ∀ l ∈ CFSG.KD.LyOm.WF3_0, l < 4 := by decide +kernel
theorem wf31_lt : ∀ l ∈ CFSG.KD.LyOm.WF3_1, l < 4 := by decide +kernel
theorem wf40_lt : ∀ l ∈ CFSG.KD.LyOm.WF4_0, l < 4 := by decide +kernel
theorem wf41_lt : ∀ l ∈ CFSG.KD.LyOm.WF4_1, l < 4 := by decide +kernel

theorem s3_parts : CFSG.KD.LyS3.m = 2 ∧ pickL CFSG.KD.LyS3.KS 0 = CFSG.KD.LyOm.KQ0 ∧
    pickL CFSG.KD.LyS3.KS 1 = CFSG.KD.LyOm.KQ1 ∧
    getRec CFSG.KD.LyS3.KX 539 0 = CFSG.KD.LyOm.BE3 := by
  have h := CFSG.KD.LyOm.s3
  generalize h1 : CFSG.KD.LyS3.m = m at h
  generalize h2 : pickL CFSG.KD.LyS3.KS 0 = k0 at h
  generalize h3 : pickL CFSG.KD.LyS3.KS 1 = k1 at h
  generalize h4 : getRec CFSG.KD.LyS3.KX 539 0 = r at h
  generalize h5 : CFSG.KD.LyOm.KQ0 = q0 at h
  generalize h6 : CFSG.KD.LyOm.KQ1 = q1 at h
  generalize h7 : CFSG.KD.LyOm.BE3 = b at h
  obtain ⟨a1, h⟩ := bAnd_true h
  obtain ⟨a2, h⟩ := bAnd_true h
  obtain ⟨a3, a4⟩ := bAnd_true h
  subst h5 h6 h7
  exact ⟨beq_eq a1, beq_eq a2, beq_eq a3, beq_eq a4⟩

theorem s4_parts : CFSG.KD.LyS4.m = 2 ∧ pickL CFSG.KD.LyS4.KS 0 = CFSG.KD.LyOm.KQ0 ∧
    pickL CFSG.KD.LyS4.KS 1 = CFSG.KD.LyOm.KQ1 ∧
    getRec CFSG.KD.LyS4.KX 539 0 = CFSG.KD.LyOm.BE4 := by
  have h := CFSG.KD.LyOm.s4
  generalize h1 : CFSG.KD.LyS4.m = m at h
  generalize h2 : pickL CFSG.KD.LyS4.KS 0 = k0 at h
  generalize h3 : pickL CFSG.KD.LyS4.KS 1 = k1 at h
  generalize h4 : getRec CFSG.KD.LyS4.KX 539 0 = r at h
  generalize h5 : CFSG.KD.LyOm.KQ0 = q0 at h
  generalize h6 : CFSG.KD.LyOm.KQ1 = q1 at h
  generalize h7 : CFSG.KD.LyOm.BE4 = b at h
  obtain ⟨a1, h⟩ := bAnd_true h
  obtain ⟨a2, h⟩ := bAnd_true h
  obtain ⟨a3, a4⟩ := bAnd_true h
  subst h5 h6 h7
  exact ⟨beq_eq a1, beq_eq a2, beq_eq a3, beq_eq a4⟩

theorem beta_rep3
    [LySeed] : beta (gRep 3 • opE) = fm CFSG.KD.LyOm.BE3 := by
  ext1
  rw [fm_smM, rep3.2.2.2.2]

theorem beta_rep4
    [LySeed] : beta (gRep 4 • opE) = fm CFSG.KD.LyOm.BE4 := by
  ext1
  rw [fm_smM, rep4.2.2.2.2]

theorem card_orbit_o3_pair
    [LySeed] :
    2034375 ≤ Nat.card (orbit lyH (pairOp (gRep 3 • opE))) := by
  obtain ⟨hm, hK0, hK1, hr⟩ := s3_parts
  obtain ⟨cUT, eUT, -, cBE, -⟩ := rep3
  obtain ⟨hA, hAi⟩ := small_tree (KX := CFSG.KD.LyS3.KX) (PT := CFSG.KD.LyS3.PT)
    (SG := CFSG.KD.LyS3.SG) (KS := CFSG.KD.LyS3.KS) (m := CFSG.KD.LyS3.m) (n := CFSG.KD.LyS3.n)
    (nl := CFSG.KD.LyS3.nl) hm hK0 hK1 hr cBE (by rw [CFSG.KD.LyS3.n_eq, CFSG.KD.LyS3.nl_eq]; norm_num)
    (fun b hb => CFSG.KD.LyS3.leavesOK b (by
      rw [CFSG.KD.LyS3.nl_eq] at hb
      change b < 6358
      exact hb))
    (fun k hk => by
      have hk' := hk
      rw [CFSG.KD.LyS3.n_eq] at hk'
      by_cases hl : k < 405504
      · exact (sSort_sound (CFSG.KD.LyS3.sortsOK (k / 4096) (by change k / 4096 < 99; omega)) k
          (by omega) (by omega)).1
      · by_cases hm' : k < 406874
        · exact (sSort_sound CFSG.KD.LyS3.s3s99 k (by change 405504 ≤ k; omega)
            (by change k < 405504 + 1370; omega)).1
        · have : k = 406873 + 1 := by omega
          rw [this]
          exact (sSort_sound CFSG.KD.LyS3.s3s99 406873 (by change 405504 ≤ 406873; omega)
            (by change 406873 < 405504 + 1370; omega)).2.1)
    (fun k hk => by
      rw [CFSG.KD.LyS3.n_eq] at hk
      by_cases hl : k < 405504
      · exact (sSort_sound (CFSG.KD.LyS3.sortsOK (k / 4096) (by change k / 4096 < 99; omega)) k
          (by omega) (by omega)).2.2
      · exact (sSort_sound CFSG.KD.LyS3.s3s99 k (by change 405504 ≤ k; omega)
          (by change k < 405504 + 1370; omega)).2.2)
  obtain ⟨sp, hB, hBi⟩ := fiber_tree (KX := CFSG.KD.LyF3.KX) (PT := CFSG.KD.LyF3.PT)
    (WT := CFSG.KD.LyF3.WT) (GT := CFSG.KD.LyF3.GT) (WC := CFSG.KD.LyF3.WC)
    (PI := CFSG.KD.LyF3.PI) (PJ := CFSG.KD.LyF3.PJ) (SG := CFSG.KD.LyF3.SG) (n := CFSG.KD.LyF3.n)
    (nc := CFSG.KD.LyF3.nc) (F := fm CFSG.KD.LyOm.BE3) CFSG.KD.LyF3.nc_eq wf30_lt wf31_lt
    (fixBeta_stab wf30_lt cBE CFSG.KD.LyOm.fw3_0) (fixBeta_stab wf31_lt cBE CFSG.KD.LyOm.fw3_1)
    CFSG.KD.LyOm.f3pi CFSG.KD.LyOm.f3gt CFSG.KD.LyOm.f3wc
    (fun i hi => cRange_sound CFSG.KD.LyF3.f30 i (by change 64 * 0 ≤ i; omega) (by
      rw [CFSG.KD.LyF3.n_eq] at hi
      change i < 64 * (0 + 1)
      omega) hi)
    (fun k hk => by
      have hk' := hk
      rw [CFSG.KD.LyF3.n_eq] at hk'
      by_cases hm' : k < 4
      · exact (cSort_sound CFSG.KD.LyF3.f3s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 4; omega)).1
      · have : k = 3 + 1 := by omega
        rw [this]
        exact (cSort_sound CFSG.KD.LyF3.f3s0 3 (by change 0 ≤ 3; omega)
          (by change 3 < 0 + 4; omega)).2.1)
    (fun k hk => by
      rw [CFSG.KD.LyF3.n_eq] at hk
      exact (cSort_sound CFSG.KD.LyF3.f3s0 k (by change 0 ≤ k; omega)
        (by change k < 0 + 4; omega)).2.2)
    (by rw [CFSG.KD.LyF3.n_eq]; norm_num) cUT eUT CFSG.KD.LyOm.f3root
  have h := card_of_fiber_pair (gRep 3 • opE) _ _ hA hAi sp hB hBi
  rw [CFSG.KD.LyS3.n_eq, CFSG.KD.LyF3.n_eq] at h
  unfold pairOp
  rw [beta_rep3]
  exact h

theorem card_orbit_o3
    [LySeed] : 2034375 ≤ Nat.card (orbit lyH (gRep 3 • opE)) :=
  card_orbit_o3_pair.trans (card_orbit_le_of_map pairOp pairOp_smulH _)

theorem card_orbit_o4_pair
    [LySeed] :
    5812500 ≤ Nat.card (orbit lyH (pairOp (gRep 4 • opE))) := by
  obtain ⟨hm, hK0, hK1, hr⟩ := s4_parts
  obtain ⟨cUT, eUT, -, cBE, -⟩ := rep4
  obtain ⟨hA, hAi⟩ := small_tree (KX := CFSG.KD.LyS4.KX) (PT := CFSG.KD.LyS4.PT)
    (SG := CFSG.KD.LyS4.SG) (KS := CFSG.KD.LyS4.KS) (m := CFSG.KD.LyS4.m) (n := CFSG.KD.LyS4.n)
    (nl := 122) hm hK0 hK1 hr cBE (by rw [CFSG.KD.LyS4.n_eq]; norm_num)
    (fun b hb => CFSG.KD.LyS4.leavesOK b (by change b < 122; exact hb))
    (fun k hk => by
      have hk' := hk
      rw [CFSG.KD.LyS4.n_eq] at hk'
      by_cases hl : k < 4096
      · exact (sSort_sound CFSG.KD.LyS4.s4s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 4096; omega)).1
      · by_cases hm' : k < 7749
        · exact (sSort_sound CFSG.KD.LyS4.s4s1 k (by change 4096 ≤ k; omega)
            (by change k < 4096 + 3653; omega)).1
        · have : k = 7748 + 1 := by omega
          rw [this]
          exact (sSort_sound CFSG.KD.LyS4.s4s1 7748 (by change 4096 ≤ 7748; omega)
            (by change 7748 < 4096 + 3653; omega)).2.1)
    (fun k hk => by
      rw [CFSG.KD.LyS4.n_eq] at hk
      by_cases hl : k < 4096
      · exact (sSort_sound CFSG.KD.LyS4.s4s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 4096; omega)).2.2
      · exact (sSort_sound CFSG.KD.LyS4.s4s1 k (by change 4096 ≤ k; omega)
          (by change k < 4096 + 3653; omega)).2.2)
  obtain ⟨sp, hB, hBi⟩ := fiber_tree (KX := CFSG.KD.LyF4.KX) (PT := CFSG.KD.LyF4.PT)
    (WT := CFSG.KD.LyF4.WT) (GT := CFSG.KD.LyF4.GT) (WC := CFSG.KD.LyF4.WC)
    (PI := CFSG.KD.LyF4.PI) (PJ := CFSG.KD.LyF4.PJ) (SG := CFSG.KD.LyF4.SG) (n := CFSG.KD.LyF4.n)
    (nc := CFSG.KD.LyF4.nc) (F := fm CFSG.KD.LyOm.BE4) CFSG.KD.LyF4.nc_eq wf40_lt wf41_lt
    (fixBeta_stab wf40_lt cBE CFSG.KD.LyOm.fw4_0) (fixBeta_stab wf41_lt cBE CFSG.KD.LyOm.fw4_1)
    CFSG.KD.LyOm.f4pi CFSG.KD.LyOm.f4gt CFSG.KD.LyOm.f4wc
    (fun i hi => cRange_sound (CFSG.KD.LyF4.leavesOK (i / 64) (by
      rw [CFSG.KD.LyF4.n_eq] at hi
      change i / 64 < 12
      omega)) i (by omega) (by omega) hi)
    (fun k hk => by
      have hk' := hk
      rw [CFSG.KD.LyF4.n_eq] at hk'
      by_cases hm' : k < 749
      · exact (cSort_sound CFSG.KD.LyF4.f4s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 749; omega)).1
      · have : k = 748 + 1 := by omega
        rw [this]
        exact (cSort_sound CFSG.KD.LyF4.f4s0 748 (by change 0 ≤ 748; omega)
          (by change 748 < 0 + 749; omega)).2.1)
    (fun k hk => by
      rw [CFSG.KD.LyF4.n_eq] at hk
      exact (cSort_sound CFSG.KD.LyF4.f4s0 k (by change 0 ≤ k; omega)
        (by change k < 0 + 749; omega)).2.2)
    (by rw [CFSG.KD.LyF4.n_eq]; norm_num) cUT eUT CFSG.KD.LyOm.f4root
  have h := card_of_fiber_pair (gRep 4 • opE) _ _ hA hAi sp hB hBi
  rw [CFSG.KD.LyS4.n_eq, CFSG.KD.LyF4.n_eq] at h
  unfold pairOp
  rw [beta_rep4]
  exact h

theorem card_orbit_o4
    [LySeed] : 5812500 ≤ Nat.card (orbit lyH (gRep 4 • opE)) :=
  card_orbit_o4_pair.trans (card_orbit_le_of_map pairOp pairOp_smulH _)

end CertificateChecks.KernelLy.Omega

end

end
