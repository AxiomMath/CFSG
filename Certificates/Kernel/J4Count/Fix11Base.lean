
module

public import Certificates.Kernel.J4Count.Checks11
public import Certificates.Kernel.J4Count.SuborbBase
public import CFSG.Certificates.Kernel.J4SlpSound
public import CFSG.Sporadic.Schreier.J4SElevenBase

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ MulAction
open CFSG.KC.J4Slp CFSG.KS.SporSch.J4B CFSG.KC.J4Q CFSG.KD.J4Q
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CertificateChecks.KernelSporSch

theorem init_ok : RegsOK 7 (initRegsN O 7 An Bn) (initK one A A B Bi) := by
  refine ⟨Array.size_ofFn, rfl, fun r hr => ?_⟩
  interval_cases r
  · exact oneP_ok J4Real.hK
  · exact J4InvP.pA
  · exact J4InvP.pB
  · exact oneP_ok J4Real.hK
  · exact oneP_ok J4Real.hK
  · exact oneP_ok J4Real.hK
  · exact oneP_ok J4Real.hK

section Run

theorem regs11 : RegsOK 7 max7Regs R11 := by
  have h := runK_ok J4Real.hK init_ok max7Prog max7Prog_lt
  rw [max7Prog_code] at h
  exact h

theorem chk_facts : O.vmul P1K QXn.1 = P1K ∧ O.vmul P1K QZn.1 % 2 ^ 112 ≠ P1K :=
  chk11_sound J4Real.hK (regs11.2.2 1 (by norm_num)) (regs11.2.2 2 (by norm_num)) fix11

noncomputable abbrev p₁ : Row := toRow (toVecD 112 P1K)

theorem P1K_lt : P1K < 2 ^ 112 := by
  have h := p1_lt
  rw [Nat.blt_eq] at h
  exact h

noncomputable abbrev m₁ : J := signedWord a b wordP1

end Run

section Bound

theorem eleven_sizes : ∀ s ∈ L7, 11 ∣ 501397585920 / s → s = 1 ∨ s = 82575360 := by
  decide +kernel

theorem L7_pos : ∀ s ∈ L7, 0 < s := by decide

theorem idx_le : ∀ d ∈ Nat.divisors 6072, d % 11 = 1 → d ≤ 276 := by decide +kernel

end Bound

section Main

noncomputable abbrev h₁ : J := m₁ * qx * m₁⁻¹

theorem isConj_qx_h1 : IsConj qx h₁ := isConj_iff.2 ⟨m₁, rfl⟩

noncomputable abbrev fixX : Set Row := {w | w ∈ orbit J v ∧ qx • w = w}

end Main

end CertificateChecks.KernelJ4Count

end
