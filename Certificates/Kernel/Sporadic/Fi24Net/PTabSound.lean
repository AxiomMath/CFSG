module

public import Certificates.Kernel.Sporadic.Fi24Net.PTabCk
public import Certificates.Kernel.Sporadic.Fi24Net.G
public import CFSG.Certificates.Kernel.Spor.Fi24NetSound
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.Fi24Net

open CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KS.Fi24Net
  CFSG.KS.Fi24NetPt

#kc_forall_tree nAllT (fun j => CFSG.KD.Fi24Net.nck j = true) 13 CFSG.KD.Fi24Net.Ck.n
#kc_forall_tree tfAll (fun g => CFSG.KD.Fi24Net.tckF g = true) 247 CFSG.KD.Fi24Net.Ck.tf
#kc_forall_tree trAll (fun g => CFSG.KD.Fi24Net.tckR g = true) 247 CFSG.KD.Fi24Net.Ck.tr

theorem ldist_symm : ∀ l < 37, ldist l = ldist (36 - l) := by decide

theorem nv_NWr {j : Nat} (hv : NV (NW j)) : NV (NWr j) := by
  intro l hl
  have h := hv (36 - l) (by omega)
  unfold NWr
  rw [ldist_symm l hl]
  exact h

theorem pF_NWr (j : Nat) : pF (NWr j) = pR (NW j) := by
  funext q
  unfold pF pR
  refine compF_congr 0 37 (fun i _ hi => ?_) q
  unfold NWr
  rw [ldist_symm i (by omega)]
  rfl

theorem tab_planes {j : Nat} (hj : j < 13) :
    (∀ k < 19, genOK (PTj j) (NW j) 0 k = true) ∧ (∀ k < 19, genOK (PTj j) (NWr j) 19 k = true) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hg : 19 * j + k < 247 := by omega
    have h := tfAll (19 * j + k) hg
    have e1 : (19 * j + k) / 19 = j := by omega
    have e2 : (19 * j + k) % 19 = k := by omega
    change genOK (PTj ((19 * j + k) / 19)) (NW ((19 * j + k) / 19)) 0 ((19 * j + k) % 19) = true at h
    rw [e1, e2] at h
    exact h
  · have hg : 19 * j + k < 247 := by omega
    have h := trAll (19 * j + k) hg
    have e1 : (19 * j + k) / 19 = j := by omega
    have e2 : (19 * j + k) % 19 = k := by omega
    change genOK (PTj ((19 * j + k) / 19)) (NWr ((19 * j + k) / 19)) 19 ((19 * j + k) % 19) = true at h
    rw [e1, e2] at h
    exact h

theorem tab_fwd {j x : Nat} (hj : j < 13) (hx : x < 306936) :
    Nat.land (ptRec j x) 524287 = pF (NW j) x := by
  have hv := (net_spec (nAllT j hj)).1
  rw [gen_alpha hv (tab_planes hj).1 hx]
  rfl

theorem tab_rev {j x : Nat} (hj : j < 13) (hx : x < 306936) :
    Nat.land (Nat.shiftRight (ptRec j x) 19) 524287 = pR (NW j) x := by
  have hv := nv_NWr (net_spec (nAllT j hj)).1
  rw [← pF_NWr, gen_beta hv (tab_planes hj).2 hx]
  rfl

theorem letPT_eq : letPT = letN NW := by
  funext l x
  unfold letPT
  by_cases h : x < 306936 ∧ l < 26
  · have hc : andB (Nat.blt x 306936) (Nat.blt l 26) = true := by
      rw [Nat.blt_eq.mpr h.1, Nat.blt_eq.mpr h.2]
      rfl
    rw [hc, CFSG.KS.Fi24NetPt.strictN_eq, letN_eq]
    have hj : l / 2 < 13 := by omega
    have hs : Nat.shiftRight l 1 = l / 2 := shr_one l
    rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
    · have e0 : Nat.beq (Nat.land (2 * j) 1) 0 = true := by
        rw [land_one]
        simp
      have ej : 2 * j / 2 = j := by omega
      rw [hs, e0, ej, LN_even]
      exact tab_fwd (by omega) h.1
    · have e0 : Nat.beq (Nat.land (2 * j + 1) 1) 0 = false := by
        rw [land_one]
        simp only [Nat.mul_add_mod, Nat.one_mod]
        rfl
      have ej : (2 * j + 1) / 2 = j := by omega
      rw [hs, e0, ej, LN_odd]
      exact tab_rev (by omega) h.1
  · have hc : andB (Nat.blt x 306936) (Nat.blt l 26) = false := by
      cases e1 : Nat.blt x 306936 <;> cases e2 : Nat.blt l 26
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨Nat.blt_eq.mp e1, Nat.blt_eq.mp e2⟩ h
    rw [hc]

end CFSG.KD.Fi24Net

end
