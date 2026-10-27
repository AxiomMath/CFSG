module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanFi22AltData
public import Certificates.Kernel.Fi22Alt.Defs
public import CFSG.Certificates.Kernel.Spor.TabWords
import Certificates.Kernel.Fi22Alt.Checks
import Certificates.Kernel.Fi22Guest.Final
import Certificates.Kernel.Fi22Core.OrbData
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RelTR
import CFSG.Certificates.Kernel.Fi22.LettersSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.Loops
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelFi22Alt.altAll CertificateChecks.KernelFi22Alt.altSl 71

namespace CertificateChecks.KernelFi22Alt

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.RelTR CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Fi22.Native CFSG.AGLEmbedding.KFactProofs.Fi22Guest
  CFSG.AGLEmbedding.KFactProofs.Fi22Alt CertificateChecks.KernelFi22Guest

theorem xData_ok : ∀ i < 7, ∀ s ∈ List.getD xData i [], s ≠ 0 ∧ s.natAbs ≤ 18 := by
  decide +kernel

theorem xTab_TR {i : Nat} (hi : i < 7) :
    TR 3510 (xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) i) (xComp i) := by
  unfold xTab
  exact eFold_TR (xData_ok i hi)

theorem moore_of {X : Nat → Table} (hX : ∀ i < 8, TR 3510 (X i) (xM i)) :
    mooreChecks 3510 X = true := by
  unfold mooreChecks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [beq_iff_eq]
    refine eq_idT_of_TR (by norm_num) (powT_TR (by norm_num) (hX 1 (by norm_num)) 3)
      fun x hx => ?_
    have h := altAll 0 (by change 0 < 71; omega)
    unfold altSl at h
    rw [Raw.Orb.bIf_eq, if_pos (Nat.beq_refl 0)] at h
    exact Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h x hx)
  · rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases h2 : j < 2
    · exact Or.inl h2
    · right
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
      have h := altAll (j - 1) (by change j - 1 < 71; omega)
      unfold altSl at h
      have e0 : ¬Nat.beq (j - 1) 0 = true := fun e => by
        have := Nat.eq_of_beq_eq_true e
        omega
      have e7 : Nat.blt (j - 1) 7 = true := Nat.blt_eq.mpr (by omega)
      have es : Nat.succ (j - 1) = j := by omega
      rw [Raw.Orb.bIf_eq, if_neg e0, Raw.Orb.bIf_eq, if_pos e7, es] at h
      have hp : ∀ x < 3510, iterK (xM j) 2 x = x ∧
          iterK (fun z => xM (j - 1) (xM j z)) 3 x = x := fun x hx => by
        have h' := Raw.Orb.allN_iff.1 h x hx
        rw [bAnd_iff] at h'
        exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2⟩
      exact ⟨eq_idT_of_TR (by norm_num) (powT_TR (by norm_num) (hX j (by omega)) 2)
          fun x hx => (hp x hx).1,
        eq_idT_of_TR (by norm_num) (powT_TR (by norm_num)
          (compT_TR (hX (j - 1) (by omega)) (hX j (by omega))) 3) fun x hx => (hp x hx).2⟩
  · rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range] at hi
    rw [List.all_eq_true]
    intro j hj
    rw [List.mem_range] at hj
    rw [Bool.or_eq_true, decide_eq_true_eq]
    by_cases hij : i < 1 ∨ j < i + 2
    · exact Or.inl hij
    · right
      rw [beq_iff_eq]
      have h := altAll (7 + 8 * i + j) (by change 7 + 8 * i + j < 71; omega)
      unfold altSl at h
      have e0 : ¬Nat.beq (7 + 8 * i + j) 0 = true := fun e => by
        have := Nat.eq_of_beq_eq_true e
        omega
      have e7 : ¬Nat.blt (7 + 8 * i + j) 7 = true := fun e => by
        have := Nat.blt_eq.mp e
        omega
      have e1 : Nat.div (Nat.sub (7 + 8 * i + j) 7) 8 = i := by
        change (7 + 8 * i + j - 7) / 8 = i
        omega
      have e2 : Nat.mod (Nat.sub (7 + 8 * i + j) 7) 8 = j := by
        change (7 + 8 * i + j - 7) % 8 = j
        omega
      have e3 : ¬Nat.blt i 1 = true := fun e => by
        have := Nat.blt_eq.mp e
        omega
      have e4 : ¬Nat.blt j (Nat.add i 2) = true := fun e => by
        have := Nat.blt_eq.mp e
        change j < i + 2 at this
        omega
      rw [Raw.Orb.bIf_eq, if_neg e0, Raw.Orb.bIf_eq, if_neg e7, e1, e2, Raw.Orb.bIf_eq, if_neg e3,
        Raw.Orb.bIf_eq, if_neg e4] at h
      exact eq_idT_of_TR (by norm_num) (powT_TR (by norm_num)
        (compT_TR (hX i (by omega)) (hX j (by omega))) 2)
        fun x hx => Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 h x hx)
  · obtain ⟨w, hw, hf⟩ := movesK_spec (f := xM 1) mv_ok
    exact movesPt_of (hX 1 (by norm_num)) hw hf

theorem X_TR {i : Nat} (hi : i < 8) :
    TR 3510 ([xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 0,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 0,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 1,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 2,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 3,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 4,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 5,
      xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 6].getD i
      (xTab 3510 orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) 0)) (xM i) := by
  interval_cases i <;> simp only [List.getD_cons_succ, List.getD_cons_zero] <;>
    exact xTab_TR (by norm_num)

theorem alt_ok : fi22AltCheck = true := by
  unfold fi22AltCheck
  rw [CertificateChecks.KernelFi22C.orbitData_eq]
  unfold altCheck
  exact moore_of fun i hi => X_TR hi

end CertificateChecks.KernelFi22Alt

end
