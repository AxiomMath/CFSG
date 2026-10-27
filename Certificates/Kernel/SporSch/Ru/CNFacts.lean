
module

public import Certificates.Kernel.SporSch.Ru.CChain
public import Certificates.Kernel.SporSch.Ru.NChain
public import Certificates.Kernel.SporSch.Ru.C2253P
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuCNF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuLines

theorem sC : allN 7 (fun j => Nat.beq (RuCS.S j) (RuT4060.L (Nat.add 2 j))) = true := by quickRfl
theorem sN : allN 6 (fun j => Nat.beq (RuNS.S j) (RuT4060.L (Nat.add 9 j))) = true := by quickRfl
theorem bC : allN 3 (fun t => Nat.beq (ruBaseArr 4060 ruCBase)[t]!
    (pg 12 (mask 12) RuCS.BP t)) = true := by quickRfl
theorem bN : allN 3 (fun t => Nat.beq (ruBaseArr 4060 ruNBase)[t]!
    (pg 12 (mask 12) RuNS.BP t)) = true := by quickRfl
theorem pC : allN 7 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuCS.S j) (RuCS.SI j)) =
    true := by quickRfl
theorem pN : allN 6 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuNS.S j) (RuNS.SI j)) =
    true := by quickRfl
theorem cC0 : Nat.beq (rcnt (RuCS.LR 0)) 1920 = true := by quickRfl
theorem cC1 : Nat.beq (rcnt (RuCS.LR 1)) 64 = true := by quickRfl
theorem cC2 : Nat.beq (rcnt (RuCS.LR 2)) 2 = true := by quickRfl
theorem cN0 : Nat.beq (rcnt (RuNS.LR 0)) 3584 = true := by quickRfl
theorem cN1 : Nat.beq (rcnt (RuNS.LR 1)) 48 = true := by quickRfl
theorem cN2 : Nat.beq (rcnt (RuNS.LR 2)) 2 = true := by quickRfl

@[expose] noncomputable def siftS (i : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (RuG.SG i) (4060 * 12)) 0,
    siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuCS.LR RuCS.TRI RuCS.BP 3 0 (RuG.SG i))

@[expose] noncomputable def siftKt (i : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight (RuCe.KG i) (4060 * 12)) 0,
    siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuCS.LR RuCS.TRI RuCS.BP 3 0 (RuCe.KG i))

theorem hS : allN 4 siftS = true := by quickRfl
theorem hK : allN 8 siftKt = true := by quickRfl

theorem binds4060 {f off l nb BP : Nat} {PS : Nat → Nat} {b : List Nat}
    (hs : ruLines4060.getD f (0, 0) = (off, l)) (hl : off + l ≤ 45)
    (hS : allN l (fun j => Nat.beq (PS j) (RuT4060.L (Nat.add off j))) = true)
    (hb : b.length = nb)
    (hB : allN nb (fun t => Nat.beq (ruBaseArr 4060 b)[t]! (pg 12 (mask 12) BP t)) = true) :
    Binds 4060 12 PS l nb BP (ruField4060 f) (ruBaseArr 4060 b) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, fun j hj => ?_, ?_,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hB t ht)⟩
  · rw [ruField4060, Array.size_ofFn, hs]
  · have e : PS j = RuT4060.L (Nat.add off j) := Nat.eq_of_beq_eq_true (allN_spec hS j hj)
    rw [RuCe.f4060 off l (off + j) hs hj rfl (by omega)]
    exact congrArg (unpack 4060 12) e.symm
  · simp [ruBaseArr, hb]

theorem bindsC : Binds 4060 12 RuCS.S 7 3 RuCS.BP (ruField4060 1) (ruBaseArr 4060 ruCBase) :=
  binds4060 rfl (by norm_num) sC rfl bC

theorem bindsN : Binds 4060 12 RuNS.S 6 3 RuNS.BP (ruField4060 2) (ruBaseArr 4060 ruNBase) :=
  binds4060 rfl (by norm_num) sN rfl bN

theorem le_of {a b : Nat} (h : Nat.ble a b = true) : a ≤ b := Nat.le_of_ble_eq_true h

theorem factsC : ruChainOK 4060 (ruField4060 1) 2 7 ruCBase ruCDerivations = true ∧
    rawOrbitSizes 4060 (ruField4060 1) (ruBaseArr 4060 ruCBase) = [1920, 64, 2] ∧
    (∀ i < 4, ruSift 4060 (ruField4060 1) ruCBase ruSGensA[i]! = true) ∧
    (∀ i < 8, ruSift 4060 (ruField4060 1) ruCBase ruKGensA[i]! = true) := by
  refine ⟨rawChainK_sound (NS := RuCS.NS) bindsC RuCS.head RuCS.hl (le_of (by quickRfl)) RuCS.hs,
    ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [rawOrbitSizesK_sound bindsC pC RuCS.hl]
    simp [List.range_succ, Nat.eq_of_beq_eq_true cC0, Nat.eq_of_beq_eq_true cC1,
      Nat.eq_of_beq_eq_true cC2]
  · have h := allN_spec hS i hi
    unfold siftS at h
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
    exact siftK_sound bindsC pC RuCS.hl (RuG.sg_eq hi) (range_of_canonK (allN_spec RuCe.cSG i hi))
      h2
  · have h := allN_spec hK i hi
    unfold siftKt at h
    obtain ⟨-, h2⟩ := (bAnd_iff _ _).1 h
    exact siftK_sound bindsC pC RuCS.hl (RuCe.kg_eq hi) (range_of_canonK (RuCe.kok_spec hi).2) h2

theorem factsN : ruChainOK 4060 (ruField4060 2) 2 6 ruNBase ruNDerivations = true ∧
    rawOrbitSizes 4060 (ruField4060 2) (ruBaseArr 4060 ruNBase) = [3584, 48, 2] := by
  refine ⟨rawChainK_sound (NS := RuNS.NS) bindsN RuNS.head RuNS.hl (le_of (by quickRfl)) RuNS.hs,
    ?_⟩
  rw [rawOrbitSizesK_sound bindsN pN RuNS.hl]
  simp [List.range_succ, Nat.eq_of_beq_eq_true cN0, Nat.eq_of_beq_eq_true cN1,
    Nat.eq_of_beq_eq_true cN2]

end CertificateChecks.KernelSporSch.RuCNF

end
