module

public import Certificates.Kernel.SporDet.Fi24Data
public import Certificates.Kernel.Sporadic.Fi24Br.Data
public import Certificates.Data.Kernel.Spor.F3LaneId
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelDet.Fi24

open CFSG.F3.Native CFSG.KS.F3L

set_option Elab.async false

theorem laneAp_ok : Nat.beq LA.p (Nat.land (CFSG.KD.BrFi24.RB 23) CFSG.KD.BrFi24.LO) = true := by
  quickRfl
theorem laneAm_ok : Nat.beq LA.m (Nat.shiftRight (CFSG.KD.BrFi24.RB 23) 609961) = true := by
  quickRfl
theorem laneAw_ok : LA.wf = true := by quickRfl
theorem laneBp_ok : Nat.beq LB.p (Nat.land (CFSG.KD.BrFi24.RB 24) CFSG.KD.BrFi24.LO) = true := by
  quickRfl
theorem laneBm_ok : Nat.beq LB.m (Nat.shiftRight (CFSG.KD.BrFi24.RB 24) 609961) = true := by
  quickRfl
theorem laneBw_ok : LB.wf = true := by quickRfl

theorem id_ok : idOK 781 LI = true := by decide +kernel

theorem eqV_of_beq {X Y : V} (h : X.beq Y = true) : X = Y := by
  obtain ⟨p, m⟩ := X
  obtain ⟨p', m'⟩ := Y
  simp only [V.beq, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, h.2]

theorem powF_zero (X : V) : powF X 0 = LI := rfl

theorem powF_succ (X : V) (e : Nat) : powF X (e + 1) = mulF (powF X e) X := rfl

theorem bI_ok : (mulF LI LB).beq LB = true := by quickRfl
theorem bB_ok : (mulF LB LB).beq LB2 = true := by quickRfl
theorem bC_ok : (mulF LB2 LB).beq LI = true := by quickRfl

theorem b3_ok : (powF LB 3).beq LI = true := by
  rw [powF_succ, powF_succ, powF_succ, powF_zero, eqV_of_beq bI_ok, eqV_of_beq bB_ok]
  exact bC_ok

theorem c1_ok : (mulF LA LB).beq (LC 1) = true := by quickRfl
theorem cI_ok : (mulF LI (LC 1)).beq (LC 1) = true := by quickRfl
theorem c2_ok : (mulF (LC 1) (LC 1)).beq (LC 2) = true := by quickRfl
theorem c3_ok : (mulF (LC 2) (LC 1)).beq (LC 3) = true := by quickRfl
theorem c4_ok : (mulF (LC 3) (LC 1)).beq (LC 4) = true := by quickRfl
theorem c5_ok : (mulF (LC 4) (LC 1)).beq (LC 5) = true := by quickRfl
theorem c6_ok : (mulF (LC 5) (LC 1)).beq (LC 6) = true := by quickRfl
theorem c7_ok : (mulF (LC 6) (LC 1)).beq (LC 7) = true := by quickRfl
theorem c8_ok : (mulF (LC 7) (LC 1)).beq (LC 8) = true := by quickRfl
theorem c9_ok : (mulF (LC 8) (LC 1)).beq (LC 9) = true := by quickRfl
theorem c10_ok : (mulF (LC 9) (LC 1)).beq (LC 10) = true := by quickRfl
theorem c11_ok : (mulF (LC 10) (LC 1)).beq (LC 11) = true := by quickRfl
theorem c12_ok : (mulF (LC 11) (LC 1)).beq (LC 12) = true := by quickRfl
theorem c13_ok : (mulF (LC 12) (LC 1)).beq (LC 13) = true := by quickRfl
theorem c14_ok : (mulF (LC 13) (LC 1)).beq (LC 14) = true := by quickRfl
theorem c15_ok : (mulF (LC 14) (LC 1)).beq (LC 15) = true := by quickRfl
theorem c16_ok : (mulF (LC 15) (LC 1)).beq (LC 16) = true := by quickRfl
theorem c17_ok : (mulF (LC 16) (LC 1)).beq (LC 17) = true := by quickRfl
theorem c18_ok : (mulF (LC 17) (LC 1)).beq (LC 18) = true := by quickRfl
theorem c19_ok : (mulF (LC 18) (LC 1)).beq (LC 19) = true := by quickRfl
theorem c20_ok : (mulF (LC 19) (LC 1)).beq (LC 20) = true := by quickRfl
theorem c21_ok : (mulF (LC 20) (LC 1)).beq (LC 21) = true := by quickRfl
theorem c22_ok : (mulF (LC 21) (LC 1)).beq (LC 22) = true := by quickRfl
theorem c23_ok : (mulF (LC 22) (LC 1)).beq (LC 23) = true := by quickRfl
theorem c24_ok : (mulF (LC 23) (LC 1)).beq (LC 24) = true := by quickRfl
theorem c25_ok : (mulF (LC 24) (LC 1)).beq (LC 25) = true := by quickRfl
theorem c26_ok : (mulF (LC 25) (LC 1)).beq (LC 26) = true := by quickRfl
theorem c27_ok : (mulF (LC 26) (LC 1)).beq (LC 27) = true := by quickRfl
theorem c28_ok : (mulF (LC 27) (LC 1)).beq (LC 28) = true := by quickRfl
theorem c29_ok : (mulF (LC 28) (LC 1)).beq LI = true := by quickRfl

theorem pw1 : powF (LC 1) 1 = LC 1 := by
  rw [powF_succ, powF_zero]
  exact eqV_of_beq cI_ok
theorem pw2 : powF (LC 1) 2 = LC 2 := by
  rw [powF_succ, pw1]
  exact eqV_of_beq c2_ok
theorem pw3 : powF (LC 1) 3 = LC 3 := by
  rw [powF_succ, pw2]
  exact eqV_of_beq c3_ok
theorem pw4 : powF (LC 1) 4 = LC 4 := by
  rw [powF_succ, pw3]
  exact eqV_of_beq c4_ok
theorem pw5 : powF (LC 1) 5 = LC 5 := by
  rw [powF_succ, pw4]
  exact eqV_of_beq c5_ok
theorem pw6 : powF (LC 1) 6 = LC 6 := by
  rw [powF_succ, pw5]
  exact eqV_of_beq c6_ok
theorem pw7 : powF (LC 1) 7 = LC 7 := by
  rw [powF_succ, pw6]
  exact eqV_of_beq c7_ok
theorem pw8 : powF (LC 1) 8 = LC 8 := by
  rw [powF_succ, pw7]
  exact eqV_of_beq c8_ok
theorem pw9 : powF (LC 1) 9 = LC 9 := by
  rw [powF_succ, pw8]
  exact eqV_of_beq c9_ok
theorem pw10 : powF (LC 1) 10 = LC 10 := by
  rw [powF_succ, pw9]
  exact eqV_of_beq c10_ok
theorem pw11 : powF (LC 1) 11 = LC 11 := by
  rw [powF_succ, pw10]
  exact eqV_of_beq c11_ok
theorem pw12 : powF (LC 1) 12 = LC 12 := by
  rw [powF_succ, pw11]
  exact eqV_of_beq c12_ok
theorem pw13 : powF (LC 1) 13 = LC 13 := by
  rw [powF_succ, pw12]
  exact eqV_of_beq c13_ok
theorem pw14 : powF (LC 1) 14 = LC 14 := by
  rw [powF_succ, pw13]
  exact eqV_of_beq c14_ok
theorem pw15 : powF (LC 1) 15 = LC 15 := by
  rw [powF_succ, pw14]
  exact eqV_of_beq c15_ok
theorem pw16 : powF (LC 1) 16 = LC 16 := by
  rw [powF_succ, pw15]
  exact eqV_of_beq c16_ok
theorem pw17 : powF (LC 1) 17 = LC 17 := by
  rw [powF_succ, pw16]
  exact eqV_of_beq c17_ok
theorem pw18 : powF (LC 1) 18 = LC 18 := by
  rw [powF_succ, pw17]
  exact eqV_of_beq c18_ok
theorem pw19 : powF (LC 1) 19 = LC 19 := by
  rw [powF_succ, pw18]
  exact eqV_of_beq c19_ok
theorem pw20 : powF (LC 1) 20 = LC 20 := by
  rw [powF_succ, pw19]
  exact eqV_of_beq c20_ok
theorem pw21 : powF (LC 1) 21 = LC 21 := by
  rw [powF_succ, pw20]
  exact eqV_of_beq c21_ok
theorem pw22 : powF (LC 1) 22 = LC 22 := by
  rw [powF_succ, pw21]
  exact eqV_of_beq c22_ok
theorem pw23 : powF (LC 1) 23 = LC 23 := by
  rw [powF_succ, pw22]
  exact eqV_of_beq c23_ok
theorem pw24 : powF (LC 1) 24 = LC 24 := by
  rw [powF_succ, pw23]
  exact eqV_of_beq c24_ok
theorem pw25 : powF (LC 1) 25 = LC 25 := by
  rw [powF_succ, pw24]
  exact eqV_of_beq c25_ok
theorem pw26 : powF (LC 1) 26 = LC 26 := by
  rw [powF_succ, pw25]
  exact eqV_of_beq c26_ok
theorem pw27 : powF (LC 1) 27 = LC 27 := by
  rw [powF_succ, pw26]
  exact eqV_of_beq c27_ok
theorem pw28 : powF (LC 1) 28 = LC 28 := by
  rw [powF_succ, pw27]
  exact eqV_of_beq c28_ok

theorem ab29_ok : (powF (mulF LA LB) 29).beq LI = true := by
  rw [eqV_of_beq c1_ok, powF_succ, pw28]
  exact c29_ok

end CertificateChecks.KernelDet.Fi24

end
