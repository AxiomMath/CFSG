module

public import Certificates.Kernel.SporSch.J4S.RealK
public import CFSG.Certificates.Kernel.SporSch.J4SRunSound
meta import CFSG.Sporadic.Schreier.J4SNative
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4RG CFSG.Sporadic.J4Schreier.regsN

namespace CertificateChecks.KernelSporSch.J4Regs

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.Sporadic.GLQ
open CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.J4Real

@[expose] noncomputable def INIT : List Nat :=
  [one, A, B, one, one, one, one, one, one, one, A, Bi, one, one, one, one, one, one]

theorem run : eqLK (runPK c rm one INIT typeIIProg) J4RG = true := by quickRfl

theorem lts : ∀ ins ∈ typeIIProg, ins.lt 9 = true := by decide +kernel

theorem eqLK_eq : ∀ {l₁ l₂ : List Nat}, eqLK l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | x :: xs, y :: ys, h => by
    have h' : andB (Nat.beq x y) (eqLK xs ys) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rw [Nat.eq_of_beq_eq_true h1, eqLK_eq h2]

theorem init_ok : RegOK one (initRegsN O 9 An Bn) INIT := by
  refine ⟨by simp [initRegsN], rfl, fun r hr => ?_⟩
  have e : (initRegsN O 9 An Bn)[r]! =
      if r = 1 then An else if r = 2 then Bn else (O.one, O.one) := by
    rw [getElem!_pos _ r (by simpa [initRegsN] using hr)]
    simp only [initRegsN, Array.getElem_ofFn]
  rw [e]
  have hid := CFSG.KS.SporSch.J4B.id_enc hK
  interval_cases r
  · exact ⟨hid, hid⟩
  · exact ⟨hA, hA⟩
  · exact ⟨hB, hB3⟩
  all_goals exact ⟨hid, hid⟩

theorem regs_ok : RegOK one regsN J4RG := by
  have h := runPK_ok hK typeIIProg init_ok lts
  rwa [eqLK_eq run] at h

theorem hX : (WfN Xn.1 ∧ encN Xn.1 = getN one J4RG 1) ∧ (WfN Xn.2 ∧ encN Xn.2 = getN one J4RG 10) :=
  regs_ok.2.2 1 (by omega)

theorem hY : (WfN Yn.1 ∧ encN Yn.1 = getN one J4RG 2) ∧ (WfN Yn.2 ∧ encN Yn.2 = getN one J4RG 11) :=
  regs_ok.2.2 2 (by omega)

theorem hT : (WfN Tn.1 ∧ encN Tn.1 = getN one J4RG 3) ∧ (WfN Tn.2 ∧ encN Tn.2 = getN one J4RG 12) :=
  regs_ok.2.2 3 (by omega)

end CertificateChecks.KernelSporSch.J4Regs

end
