module

public import Certificates.Kernel.Fi23P.ChkDefs
public import CFSG.Certificates.Kernel.Fi23P.Spec
import Certificates.Kernel.Fi23P.Bfs0
import Certificates.Kernel.Fi23P.Bfs1
import Certificates.Kernel.Fi23P.Bfs2
import Certificates.Kernel.Fi23P.Bfs3
import Certificates.Kernel.Fi23P.Sep0
import Certificates.Kernel.Fi23P.Sep1
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23P.bAll CFSG.KD.Fi23P.bSl 16
#kon_join CFSG.KD.Fi23P.sAll CFSG.KD.Fi23P.sSl 16

namespace CFSG.KD.Fi23P

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23P CFSG.KS.Raw.Orb

theorem slice_pt {F : Nat → Bool}
    (h : ∀ s < 16, (allN (nat_lit 2048) fun i => strictB (Nat.add (Nat.mul s (nat_lit 2048)) i)
      fun y => bIf(Nat.blt y (nat_lit 31671), F y, true)) = true) :
    ∀ y < 31671, F y = true := by
  intro y hy
  have h1 := allN_iff.1 (h (y / 2048) (by omega)) (y % 2048) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq, bIf_eq] at h1
  have e : Nat.add (Nat.mul (y / 2048) 2048) (y % 2048) = y := by
    change y / 2048 * 2048 + y % 2048 = y
    omega
  rw [e, if_pos (by simpa [Nat.blt_eq] using hy)] at h1
  exact h1

theorem bPt_all : ∀ y < 31671, bPt y = true := slice_pt bAll

theorem sPt_all : ∀ y < 31671, sPt y = true := slice_pt sAll

theorem hd_ok : bfsHd rtP offP labP posP = true := by quickRfl

theorem bfs_ok : bfsOK TG rtP offP labP genP parP posP ptsP = true := by
  unfold bfsOK
  rw [bAnd_eq, Bool.and_eq_true]
  refine ⟨hd_ok, allN_iff.2 fun y hy => ?_⟩
  have h := bPt_all y hy
  unfold bPt at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact h.1

theorem facts {y : Nat} (hy : y < 31671) : BfsFacts TG rtP offP labP genP parP posP ptsP y := by
  have h := bPt_all y hy
  unfold bPt at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact bfsAt_spec h.1

theorem dep_facts {y : Nat} (hy : y < 31671) : depP y < 100 ∧ (y = rtP (labP y) → depP y = 0) ∧
    (y ≠ rtP (labP y) → depP y = depP (parP y) + 1) := by
  have h := bPt_all y hy
  unfold bPt at h
  rw [bAnd_eq, Bool.and_eq_true] at h
  exact depAt_spec h.2

theorem hd_facts : offP 0 = 0 ∧ 0 < offP 1 ∧ offP 1 < offP 2 ∧ offP 2 < offP 3 ∧
    offP 3 = 31671 ∧ ∀ c < 3, rtP c < 31671 ∧ labP (rtP c) = c ∧ posP (rtP c) = offP c :=
  bfsHd_spec hd_ok

theorem lab_lt {y : Nat} (hy : y < 31671) : labP y < 3 := (facts hy).2.2.1

theorem lab_T {y : Nat} (hy : y < 31671) {k : Nat} (hk : gOK k = true) :
    labP (TG k y) = labP y := (facts hy).2.2.2.2.2.1 k hk

theorem rt_lt {c : Nat} (hc : c < 3) : rtP c < 31671 := (hd_facts.2.2.2.2.2 c hc).1

theorem lab_rt {c : Nat} (hc : c < 3) : labP (rtP c) = c := (hd_facts.2.2.2.2.2 c hc).2.1

theorem nonroot {y : Nat} (hy : y < 31671) (hr : y ≠ rtP (labP y)) :
    gOK (genP y) = true ∧ parP y < 31671 ∧ labP (parP y) = labP y ∧ TG (genP y) (parP y) = y ∧
      depP y = depP (parP y) + 1 := by
  have hF := facts hy
  have hp : posP y ≠ offP (labP y) := fun e => hr (hF.2.2.2.2.2.2.1 e).1
  obtain ⟨g1, g2, g3, g4, -⟩ := hF.2.2.2.2.2.2.2 hp
  exact ⟨g1, g2, g3, g4, (dep_facts hy).2.2 hr⟩

theorem root_pg {y : Nat} (hy : y < 31671) (hr : y = rtP (labP y)) : parP y = 0 ∧ genP y = 0 := by
  have hF := facts hy
  have hc := lab_lt hy
  have hp : posP y = offP (labP y) := by
    have := (hd_facts.2.2.2.2.2 (labP y) hc).2.2
    rw [← hr] at this
    exact this
  exact (hF.2.2.2.2.2.2.1 hp).2

theorem dep_lt {y : Nat} (hy : y < 31671) : depP y < 100 := (dep_facts hy).1

theorem dep_root {y : Nat} (hy : y < 31671) (hr : y = rtP (labP y)) : depP y = 0 :=
  (dep_facts hy).2.1 hr

theorem moving {y : Nat} (hy : y < 31671) (hr : y ≠ rtP (labP y)) :
    baseP (labP y) ≤ tb L 8 y ∧ tb L 8 y < baseP (labP y + 1) ∧ wS (tb L 8 y) y ≠ y := by
  have h := sPt_all y hy
  unfold sPt at h
  rw [strictB_eq, bIf_eq] at h
  have hb : Nat.beq y (rtP (labP y)) = false := by
    cases e : Nat.beq y (rtP (labP y))
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hr
  rw [hb, if_neg Bool.false_ne_true, strictB_eq] at h
  simp only [bAnd_eq, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨Nat.le_of_ble_eq_true h.1, by simpa [Nat.blt_eq] using h.2.1, fun e => ?_⟩
  have := h.2.2
  rw [e, Nat.beq_refl] at this
  exact absurd this (by decide)

end CFSG.KD.Fi23P

end
