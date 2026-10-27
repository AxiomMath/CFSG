module

public import Certificates.Kernel.I242.Gens
public import Certificates.Kernel.I242.ActChecks
public import Certificates.Kernel.OmegaEight.Aut
public import CFSG.Certificates.Kernel.PermToolSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelI242

open CFSG.KC.Enum CFSG.KC.I242 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.Monster.B.Co2.Native

theorem sig_lt : ∀ x ∈ i242Sigma, x < 2 ^ 12 := by decide

theorem sig_len : i242Sigma.length = 120 := by decide

theorem sig_get {v : Nat} (hv : v < 120) : i242Sigma.getD v 0 = pg 12 4095 (sigK i242Sigma) v := by
  have h := CFSG.KC.PermTool.pg_packA sig_lt v (by rw [sig_len]; exact hv)
  rw [List.getD_eq_getElem _ _ (by rw [sig_len]; exact hv), ← h]
  rfl

theorem sig_facts {v : Nat} (hv : v < 120) : pg 12 4095 (sigK i242Sigma) v < 3510 ∧
    pg 7 127 (sigInvK i242Sigma) (pg 12 4095 (sigK i242Sigma) v) = v := by
  have h := allN_spec kSig v hv
  simp only [bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem sigInv_facts {p : Nat} (hp : p < 3510) : pg 7 127 (sigInvK i242Sigma) p ≤ 120 ∧
    (pg 7 127 (sigInvK i242Sigma) p < 120 →
      pg 12 4095 (sigK i242Sigma) (pg 7 127 (sigInvK i242Sigma) p) = p) := by
  have h := allN_spec kSigInv p hp
  simp only [bAnd_iff, Nat.ble_eq] at h
  refine ⟨h.1, fun hl => ?_⟩
  have h2 := h.2
  have hb : Nat.blt (pg 7 127 (sigInvK i242Sigma) p) 120 = true := by rw [Nat.blt_eq]; exact hl
  rw [hb] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem find_range_some {f : Nat → Bool} {s : Nat} (h1 : f s = true)
    (h2 : ∀ u < s, f u = false) : ∀ n, s < n → (List.range n).find? f = some s
  | 0, h => absurd h (Nat.not_lt_zero s)
  | n + 1, h => by
    rw [List.range_succ, List.find?_append]
    rcases Nat.lt_or_ge s n with hs | hs
    · rw [find_range_some h1 h2 n hs]
      rfl
    · have e : s = n := by omega
      subst e
      have hn : (List.range s).find? f = none := by
        rw [List.find?_eq_none]
        intro x hx
        rw [List.mem_range] at hx
        simp [h2 x hx]
      rw [hn]
      simp [h1]

theorem sinv_get {p : Nat} (hp : p < 3510) : i242SigmaInv[p]! = pg 7 127 (sigInvK i242Sigma) p := by
  have hs : p < i242SigmaInv.size := by simp [i242SigmaInv, hp]
  rw [getElem!_pos i242SigmaInv p hs]
  simp only [i242SigmaInv, Array.getElem_ofFn]
  obtain ⟨hle, hback⟩ := sigInv_facts hp
  rcases Nat.lt_or_ge (pg 7 127 (sigInvK i242Sigma) p) 120 with hl | hl
  · have e := hback hl
    have hf : (List.range 120).find? (fun v => i242Sigma.getD v 0 == p) =
        some (pg 7 127 (sigInvK i242Sigma) p) := by
      refine find_range_some ?_ (fun u hu => ?_) 120 hl
      · rw [sig_get hl, e]
        simp
      · have hu' : u < 120 := by omega
        rw [sig_get hu']
        cases e2 : (pg 12 4095 (sigK i242Sigma) u == p)
        · rfl
        · have e3 : pg 12 4095 (sigK i242Sigma) u = p := by simpa using e2
          have := (sig_facts hu').2
          rw [e3] at this
          omega
    rw [hf]
  · have he : pg 7 127 (sigInvK i242Sigma) p = 120 := by omega
    have hf : (List.range 120).find? (fun v => i242Sigma.getD v 0 == p) = none := by
      rw [List.find?_eq_none]
      intro v hv
      rw [List.mem_range] at hv
      rw [sig_get hv]
      intro e2
      have e3 : pg 12 4095 (sigK i242Sigma) v = p := by simpa using e2
      have := (sig_facts hv).2
      rw [e3, he] at this
      omega
    rw [hf, he]

theorem y_get {r p : Nat} (hr : r < 8) (hp : p < 3510) :
    (i242YArrs[r]!)[p]! = pg 12 4095 (Y.S r) p ∧ pg 12 4095 (Y.S r) p < 3510 := by
  rw [yArrs.2 r hr, Orb.unpack_get hp]
  refine ⟨rfl, ?_⟩
  have h := range_of_permOK (allN_spec permY r (by omega))
  have h2 := allN_spec h p hp
  rwa [Nat.blt_eq] at h2

theorem gen_get {r v : Nat} (hr : r < 8) (hv : v < 120) :
    (CFSG.EvenSmallLie.OmegaEight.genArrs[r]!)[v]! = pg 9 511 (CertificateChecks.KernelO8.AP.S r) v := by
  rw [CertificateChecks.KernelO8.genAP.2 r (by omega), Orb.unpack_get (by omega)]
  rfl

theorem blt_eq_of {a b : Nat}
    (h : Bool.rec (motive := fun _ => Bool) (bIf(Nat.blt b 120, false, true)) (Nat.blt b 120)
      (Nat.blt a 120) = true) : decide (a < 120) = decide (b < 120) := by
  have e1 : decide (a < 120) = Nat.blt a 120 := by rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  have e2 : decide (b < 120) = Nat.blt b 120 := by rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
  rw [e1, e2]
  revert h
  cases Nat.blt a 120 <;> cases Nat.blt b 120 <;> simp

theorem action_k : i242ActionCheck = true := by
  unfold i242ActionCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq,
    Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨by decide, by decide⟩, by decide⟩, yArrs.1⟩, by simp [i242SigmaInv]⟩,
    fun v hv => ?_⟩, fun p hp => ?_⟩, fun r hr => ?_⟩
  · obtain ⟨h1, h2⟩ := sig_facts hv
    rw [sig_get hv, sinv_get h1]
    exact ⟨h1, h2⟩
  · obtain ⟨hle, hback⟩ := sigInv_facts hp
    rw [sinv_get hp]
    refine ⟨hle, ?_⟩
    rcases Nat.lt_or_ge (pg 7 127 (sigInvK i242Sigma) p) 120 with hl | hl
    · right
      rw [sig_get hl, hback hl]
    · left
      exact hl
  · have h := allN_spec kAct r hr
    simp only [bAnd_iff] at h
    refine ⟨fun v hv => ?_, fun p hp => ?_⟩
    · have hv' := allN_spec h.1 v hv
      simp only [bAnd_iff] at hv'
      have hx : pg 9 511 (CertificateChecks.KernelO8.AP.S r) v < 120 := by
        have h3 := hv'.1
        rwa [Nat.blt_eq] at h3
      obtain ⟨h1, -⟩ := sig_facts hv
      rw [sig_get hv, (y_get hr h1).1, gen_get hr hv, sig_get hx]
      exact Nat.eq_of_beq_eq_true hv'.2
    · have hp' := allN_spec h.2 p hp
      obtain ⟨e1, e2⟩ := y_get hr hp
      rw [e1, sinv_get e2, sinv_get hp]
      exact blt_eq_of hp'

open Certificates in
theorem cert13507 : CFSG.HardMathSupport.Solomon.Coordinator.i242ActionCheck = true := action_k

end CertificateChecks.KernelI242

end
