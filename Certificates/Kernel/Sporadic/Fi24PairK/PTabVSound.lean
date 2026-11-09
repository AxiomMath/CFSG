module

public import Certificates.Kernel.Sporadic.Fi24PairK.PTabVCk
public import Certificates.Kernel.Sporadic.Fi24Net.PTabSound
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Spor.Fi24PairPcSound

public section

namespace CFSG.KD.Fi24PairK

open CFSG.KC CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt CFSG.KS.Fi24Net
  CFSG.KS.Fi24NetPt

#kc_forall_tree tfAllV (fun g => CFSG.KD.Fi24PairK.tckFV g = true) 513 CFSG.KD.Fi24PairK.Ck.vf
#kc_forall_tree trAllV (fun g => CFSG.KD.Fi24PairK.tckRV g = true) 513 CFSG.KD.Fi24PairK.Ck.vr

theorem nv_NVr {s : Nat} (hv : CFSG.KS.Fi24Net.NV (NV (nthN netL s))) : CFSG.KS.Fi24Net.NV (NVr s) := by
  intro l hl
  have h := hv (36 - l) (by omega)
  unfold NVr
  rw [CFSG.KD.Fi24Net.ldist_symm l hl]
  exact h

theorem pF_NVr (s : Nat) : pF (NVr s) = pR (NV (nthN netL s)) := by
  funext q
  unfold pF pR
  refine compF_congr 0 37 (fun i _ hi => ?_) q
  unfold NVr
  rw [CFSG.KD.Fi24Net.ldist_symm i (by omega)]
  rfl

theorem tabV_planes {s : Nat} (hs : s < 27) :
    (∀ k < 19, genOK (PTVj s) (NV (nthN netL s)) 0 k = true) ∧
      (∀ k < 19, genOK (PTVj s) (NVr s) 19 k = true) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have hg : 19 * s + k < 513 := by omega
    have h := tfAllV (19 * s + k) hg
    have e1 : (19 * s + k) / 19 = s := by omega
    have e2 : (19 * s + k) % 19 = k := by omega
    change genOK (PTVj ((19 * s + k) / 19)) (NV (nthN netL ((19 * s + k) / 19))) 0
      ((19 * s + k) % 19) = true at h
    rw [e1, e2] at h
    exact h
  · have hg : 19 * s + k < 513 := by omega
    have h := trAllV (19 * s + k) hg
    have e1 : (19 * s + k) / 19 = s := by omega
    have e2 : (19 * s + k) % 19 = k := by omega
    change genOK (PTVj ((19 * s + k) / 19)) (NVr ((19 * s + k) / 19)) 19 ((19 * s + k) % 19) = true
      at h
    rw [e1, e2] at h
    exact h

section Nets

variable (hn : ∀ g < 27, nck g = true)
include hn

theorem tabV_fwd {s x : Nat} (hs : s < 27) (hx : x < 306936) :
    Nat.land (ptRecS s x) 524287 = pF (NV (nthN netL s)) x := by
  have hv := (net_spec (hn s hs)).1
  rw [gen_alpha hv (tabV_planes hs).1 hx]
  rfl

theorem tabV_rev {s x : Nat} (hs : s < 27) (hx : x < 306936) :
    Nat.land (Nat.shiftRight (ptRecS s x) 19) 524287 = pR (NV (nthN netL s)) x := by
  have hv := nv_NVr (net_spec (hn s hs)).1
  rw [← pF_NVr, gen_beta hv (tabV_planes hs).2 hx]
  rfl

omit hn in
theorem slotV_spec {j : Nat} (h13 : 13 ≤ j) (hj : net j = true) :
    slotV j < 27 ∧ NV (nthN netL (slotV j)) = NV j := by
  have hj' : j < 29 ∨ (75 ≤ j ∧ j < 90) := by
    unfold net at hj
    cases e1 : Nat.blt j 29 <;> cases e2 : Nat.ble 75 j <;> cases e3 : Nat.blt j 90 <;>
      simp_all [Nat.blt_eq, Nat.ble_eq, orB, andB]
  rcases hj' with hj' | ⟨h1, h2⟩
  · interval_cases j <;> exact ⟨by decide, rfl⟩
  · interval_cases j <;> exact ⟨by decide, rfl⟩

omit hn in
theorem blt13_f {j : Nat} (h : 13 ≤ j) : Nat.blt j 13 = false := by
  cases e : Nat.blt j 13
  · rfl
  · rw [Nat.blt_eq] at e
    omega

omit hn in
theorem NV_lt13 {j : Nat} (h : j < 13) : NV j = CFSG.KD.Fi24Net.NW j := by
  funext l
  unfold NV
  rw [Nat.blt_eq.mpr h]

theorem ptFT_eq : ptFT = fun j x => ptF (NV j) x := by
  funext j x
  unfold ptFT
  by_cases h : x < 306936 ∧ net j = true
  · have hc : andB (Nat.blt x 306936) (net j) = true := by
      rw [Nat.blt_eq.mpr h.1, h.2]
      rfl
    rw [hc, ptF_eq]
    unfold ptRecV
    by_cases h13 : j < 13
    · rw [Nat.blt_eq.mpr h13, NV_lt13 h13]
      exact CFSG.KD.Fi24Net.tab_fwd h13 h.1
    · obtain ⟨hs, he⟩ := slotV_spec (by omega) h.2
      rw [blt13_f (by omega), ← he]
      exact tabV_fwd hn hs h.1
  · have hc : andB (Nat.blt x 306936) (net j) = false := by
      cases e1 : Nat.blt x 306936 <;> cases e2 : net j
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨Nat.blt_eq.mp e1, e2⟩ h
    rw [hc]

theorem ptRT_eq : ptRT = fun j x => ptR (NV j) x := by
  funext j x
  unfold ptRT
  by_cases h : x < 306936 ∧ net j = true
  · have hc : andB (Nat.blt x 306936) (net j) = true := by
      rw [Nat.blt_eq.mpr h.1, h.2]
      rfl
    rw [hc, ptR_eq]
    unfold ptRecV
    by_cases h13 : j < 13
    · rw [Nat.blt_eq.mpr h13, NV_lt13 h13]
      exact CFSG.KD.Fi24Net.tab_rev h13 h.1
    · obtain ⟨hs, he⟩ := slotV_spec (by omega) h.2
      rw [blt13_f (by omega), ← he]
      exact tabV_rev hn hs h.1
  · have hc : andB (Nat.blt x 306936) (net j) = false := by
      cases e1 : Nat.blt x 306936 <;> cases e2 : net j
      · rfl
      · rfl
      · rfl
      · exact absurd ⟨Nat.blt_eq.mp e1, e2⟩ h
    rw [hc]

end Nets

end CFSG.KD.Fi24PairK

namespace CFSG.KD.Fi24PairPc

open CFSG.KC CFSG.KC.Loop CFSG.KC.Fi24PairK CFSG.KC.Fi24PairPc
open CFSG.KD.Fi24PairK (NV net nck ptFT ptRT ptFT_eq ptRT_eq)

section Nets

variable (hn : ∀ g < 27, nck g = true)
include hn

theorem ptZV_eq : ptZV = ptZ NV := by
  funext z x
  unfold ptZV ptZ
  rw [ptFT_eq hn, ptRT_eq hn]

theorem apZV_eq : apZV = apZ NV := by
  unfold apZV apZ
  rw [ptZV_eq hn]

theorem eqZV_eq : eqZV = eqZ NV := by
  unfold eqZV eqZ
  rw [apZV_eq hn]

theorem pcCkV_eq : pcCkV = pcCk NV := by
  unfold pcCkV pcCk relHdV relHd cjOneV cjOne
  rw [eqZV_eq hn]

theorem genOKV_eq : genOKV = genOK NV := by
  unfold genOKV genOK
  rw [eqZV_eq hn]

theorem cTV_eq : cTV = cT := by
  unfold cTV cT
  rw [pcCkV_eq hn, CFSG.KS.Fi24PairPc.pcCkC_eq]

theorem cAV_eq : cAV = cA := by
  unfold cAV cA
  rw [pcCkV_eq hn, CFSG.KS.Fi24PairPc.pcCkC_eq]

theorem cBV_eq : cBV = cB := by
  unfold cBV cB
  rw [pcCkV_eq hn, CFSG.KS.Fi24PairPc.pcCkC_eq]

theorem gckV_eq : gckV = gck := by
  unfold gckV gck gTV gT gAV gA gBV gB
  rw [genOKV_eq hn, CFSG.KS.Fi24PairPc.genOKC_eq]

end Nets

end CFSG.KD.Fi24PairPc

end
