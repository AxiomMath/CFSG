module

public import Certificates.Kernel.Sporadic.Fi24Pc.PTabCk
public import Certificates.Kernel.Sporadic.Fi24Pc.Checks.N
public import CFSG.Certificates.Kernel.Spor.Fi24NetSound
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.Fi24Pc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KS.Fi24Net
  CFSG.KS.Fi24NetPt

#kc_forall_tree xnAll (fun j => CFSG.KD.Fi24Pc.nck j = true) 16 CFSG.KD.Fi24Pc.Ck.n
#kc_forall_tree xtfAll (fun g => CFSG.KD.Fi24Pc.xtckF g = true) 304 CFSG.KD.Fi24Pc.Ck.xt

theorem xtab_fwd {j x : Nat} (hj : j < 16) (hx : x < 306936) :
    Nat.land (xtRec j x) 524287 = pF (XW j) x := by
  have hv := (net_spec (xnAll j hj)).1
  have hp : ∀ k < 19, genOK (XTj j) (XW j) 0 k = true := fun k hk => by
    have hg : 19 * j + k < 304 := by omega
    have h := xtfAll (19 * j + k) hg
    have e1 : (19 * j + k) / 19 = j := by omega
    have e2 : (19 * j + k) % 19 = k := by omega
    change genOK (XTj ((19 * j + k) / 19)) (XW ((19 * j + k) / 19)) 0 ((19 * j + k) % 19) = true at h
    rw [e1, e2] at h
    exact h
  rw [gen_alpha hv hp hx]
  rfl

theorem letPX_eq : letPX = letN XW := by
  funext l x
  unfold letPX
  by_cases h : x < 306936 ∧ l < 32 ∧ l % 2 = 0
  · obtain ⟨hx, hl, he⟩ := h
    obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j := ⟨l / 2, by omega⟩
    have e0 : Nat.beq (Nat.land (2 * j) 1) 0 = true := by
      rw [land_one]
      simp
    have hc : andB (Nat.blt x 306936) (andB (Nat.blt (2 * j) 32) (Nat.beq (Nat.land (2 * j) 1) 0)) =
        true := by
      rw [Nat.blt_eq.mpr hx, Nat.blt_eq.mpr hl, e0]
      rfl
    have hs : Nat.shiftRight (2 * j) 1 = j := by
      rw [shr_one]
      omega
    rw [hc, letN_eq, hs, LN_even]
    exact xtab_fwd (by omega) hx
  · have hc : andB (Nat.blt x 306936) (andB (Nat.blt l 32) (Nat.beq (Nat.land l 1) 0)) = false := by
      cases e1 : Nat.blt x 306936 <;> cases e2 : Nat.blt l 32 <;>
        cases e3 : Nat.beq (Nat.land l 1) 0 <;> try rfl
      exact absurd ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2,
        by rw [← land_one]; exact Nat.eq_of_beq_eq_true e3⟩ h
    rw [hc]

end CFSG.KD.Fi24Pc

end
