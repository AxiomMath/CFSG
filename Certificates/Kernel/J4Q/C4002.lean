module

public import CFSG.Sporadic.J4.QT2LocNative
public import Certificates.Kernel.J4Q.LocM
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

theorem tm_len : Nat.beq (fstsK (ptsK OR.s0)).length 276 = true := by quickRfl

@[expose] noncomputable def dK (t : Nat) : Bool :=
  (fun i m => strictB (cvK i m) fun v => EVS.all fun u => neN v u)
    (Nat.div t 276) (getN 0 (fstsK (ptsK OR.s0)) (Nat.mod t 276))

#j4q_all CFSG.KD.J4Q.DC CertificateChecks.KernelJ4Q.dK 1656

theorem chkD_ok : chkD (locMats ()) (locInvs ()) = true := by
  unfold chkD
  simp only []
  refine List.all_eq_true.2 fun l hl => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hl
  have hM := pathM_enc hi
  have hMi := pathMi_enc hi
  rw [Bool.and_eq_true]
  refine ⟨by rw [eqRows_of (mul_enc hK hM ⟨hMi.1, hMi.2.1⟩) (id_enc hK)]; exact hMi.2.2, ?_⟩
  rw [tMasks_eq]
  refine List.all_eq_true.2 fun m hmem => ?_
  obtain ⟨j, hj, hjm⟩ := getN_of_mem 0 hmem
  have hj' : j < 276 := by rw [← Nat.eq_of_beq_eq_true tm_len]; exact hj
  have hb : 276 * i + j < 1656 := by omega
  have h2 := DC.all (276 * i + j) hb
  have hdiv : Nat.div (276 * i + j) 276 = i := by
    change (276 * i + j) / 276 = i
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hj', Nat.add_zero]
  have hmod : Nat.mod (276 * i + j) 276 = j := by
    change (276 * i + j) % 276 = j
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  rw [dK] at h2
  beta_reduce at h2
  rw [hdiv, hmod, hjm, strictB_eq] at h2
  refine List.all_eq_true.2 fun u hu => ?_
  obtain ⟨hwu, hmu⟩ := evs_mem hu
  obtain ⟨hwv, hvv⟩ := conjVec_enc hi m
  rw [differs_eq hwv hwu, hvv]
  exact List.all_eq_true.1 h2 _ hmu

theorem tClosed_ok : chkTClosed = true := by
  unfold chkTClosed
  rw [tMasks_eq]
  quickRfl

theorem one_mem : (1 : Nat) ∈ tMasks := by
  rw [tMasks_eq]
  have h : (fstsK (ptsK OR.s0)).contains 1 = true := by quickRfl
  exact List.contains_iff_mem.1 h

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem c4002 : (chkTClosed = true)
    ∧ (chkD (locMats ()) (locInvs ()) = true)
    ∧ ((1 : Nat) ∈ tMasks) := ⟨tClosed_ok, chkD_ok, one_mem⟩

end CertificateChecks.KernelJ4Q

end
