module

public import Certificates.Kernel.Misc.HNHeisChecks
public import CFSG.Certificates.Kernel.Misc.HNHeisSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHNHeis

open CFSG.KC.Misc.HNHeis CFSG.KS.Misc.HNHeis CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.He.Native

local notation "U" X:max => unpackL 133 13 1729 X

theorem rowsA_eq : rowsA = U AK := by
  change rowsOf 5 133 CFSG.Sporadic.HN.Native.seedA = _
  rw [HNSeedA.eq, payRunP_eq (w := 13) (S := 1729) _ (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem rowsB_eq : rowsB = U BK := by
  change rowsOf 5 133 CFSG.Sporadic.HN.Native.seedB = _
  rw [HNSeedB.eq, payRunP_eq (w := 13) (S := 1729) _ (by norm_num) (by norm_num) (by norm_num)]
  rfl

theorem vAK : vldH AK = true := by
  have h := seeds_ok
  rw [Bool.and_eq_true] at h
  exact h.1

theorem vBK : vldH BK = true := by
  have h := seeds_ok
  rw [Bool.and_eq_true] at h
  exact h.2

theorem init_rep : RegRep #[rowsA, rowsB] [AK, BK] := pair_rep consts_ok rowsA_eq rowsB_eq vAK vBK

theorem regs_rep : RegRep (hnSlpM hnHeisProg) RK := by
  have h := slp_rep consts_ok hnHeisProg _ _ init_rep
  unfold hnSlpM
  unfold RK slpH
  exact h

theorem rel_eq (u v : List Nat) : hnRelOK (hnSlpM hnHeisProg) u v = relH RK u v := by
  unfold hnRelOK relH
  obtain ⟨e1, v1⟩ := wordM_eq consts_ok regs_rep u
  obtain ⟨e2, v2⟩ := wordM_eq consts_ok regs_rep v
  rw [e1, e2, beqH_eq consts_ok v1 v2]

theorem hnHeisCheck_true : hnHeisCheck () = true := by
  have h := heis_ok
  have hz : Nat.beq (regH RK (hnHeisZ - 1)) ONEH = false := by
    simp only [Bool.and_eq_true] at h
    simpa using h.2
  obtain ⟨ez, vz⟩ := regs_rep.2 (hnHeisZ - 1)
  unfold hnHeisCheck
  simp only [rel_eq]
  rw [ez, notIdM_eq consts_ok vz hz]
  rw [hz] at h
  simpa using h

end CertificateChecks.KernelHNHeis

end
