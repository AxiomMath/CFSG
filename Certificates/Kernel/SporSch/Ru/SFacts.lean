module

public import Certificates.Kernel.SporSch.Ru.SChain
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuSF2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuLines

theorem sS : allN 6 (fun j => Nat.beq (RuSS.S j) (RuT4060.L (Nat.add 33 j))) = true := by quickRfl
theorem bS : allN 2 (fun t => Nat.beq (ruBaseArr 4060 ruS4060ChainBase)[t]!
    (pg 12 (mask 12) RuSS.BP t)) = true := by quickRfl
theorem pS : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuSS.S j) (RuSS.SI j)) =
    true := by quickRfl
theorem cS0 : Nat.beq (rcnt (RuSS.LR 0)) 2048 = true := by quickRfl
theorem cS1 : Nat.beq (rcnt (RuSS.LR 1)) 8 = true := by quickRfl
theorem gS : allN 4 (fun i => Nat.beq (RuT4060.L (Nat.add 33 i)) (RuG.SG i)) = true := by quickRfl

theorem le_of {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem field4_get {j : Nat} (hj : j < 6) : (ruField4060 4)[j]! = unpack 4060 12 (RuT4060.L (33 + j)) := by
  have hl : ruLines4060.getD 4 (0, 0) = (33, 6) := rfl
  have hj' : j < (ruLines4060.getD 4 (0, 0)).2 := by
    rw [hl]
    exact hj
  rw [ruField4060, getElem!_pos _ j (by simpa using hj'), Array.getElem_ofFn]
  change ruArr4060 (33 + j) = _
  exact row4060 (by omega)

theorem bindsS : Binds 4060 12 RuSS.S 6 2 RuSS.BP (ruField4060 4)
    (ruBaseArr 4060 ruS4060ChainBase) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, ?_,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec bS t ht)⟩
  · rw [ruField4060, Array.size_ofFn]
    rfl
  · rw [field4_get hj]
    exact congrArg (unpack 4060 12) (Nat.eq_of_beq_eq_true (allN_spec sS j hj)).symm
  · rfl

theorem factsS : ruChainOK 4060 (ruField4060 4) 4 6 ruS4060ChainBase ruS4060ChainDerivations =
      true ∧
    rawOrbitSizes 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) = [2048, 8] ∧
    (∀ i < 4, eqA 4060 (ruField4060 4)[i]! ruSGensA[i]! = true) := by
  refine ⟨rawChainK_sound (NS := RuSS.NS) bindsS RuSS.head RuSS.hl (le_of (by quickRfl)) RuSS.hs,
    ?_, fun i hi => ?_⟩
  · rw [rawOrbitSizesK_sound bindsS pS RuSS.hl]
    simp [List.range_succ, Nat.eq_of_beq_eq_true cS0, Nat.eq_of_beq_eq_true cS1]
  · rw [field4_get (by omega), RuG.sg_eq hi, ← Nat.eq_of_beq_eq_true (allN_spec gS i hi)]
    exact eqK_sound (Nat.beq_refl _)

end CertificateChecks.KernelSporSch.RuSF2

end
