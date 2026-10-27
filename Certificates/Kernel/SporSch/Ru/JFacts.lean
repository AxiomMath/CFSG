
module

public import Certificates.Kernel.SporSch.Ru.JChain
public import Certificates.Kernel.SporSch.Ru.JOrb
public import Certificates.Kernel.SporSch.Ru.PresBound
public import Certificates.Kernel.SporSch.Ru.Basic2247
public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.Certificates.Kernel.Spor.RawOrbSound
public import CFSG.Sporadic.Schreier.RuLocalFactsBase
public import CFSG.Sporadic.Schreier.RuCertData
import CFSG.Sporadic.Presentation.RuExactInputs
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Schreier.RuChainSpec
public import CFSG.Sporadic.Schreier.RuCheckLocalBase
public import CFSG.Sporadic.Schreier.RuCheckOrbitsBase
public import CFSG.Sporadic.Schreier.RuRestrictBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuJ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuLines

theorem sOKJ : allN 18 (fun j => Nat.beq (RuJS.S j) (RuT4060.L (Nat.add 15 j))) = true := by
  quickRfl

theorem sOKO : allN 18 (fun j => Nat.beq (RuJO.S j) (RuT4060.L (Nat.add 15 j))) = true := by
  quickRfl

theorem baseOKJ : allN 4 (fun t => Nat.beq (ruBaseArr 4060 ruJoinBase)[t]!
    (pg 12 (mask 12) RuJS.BP t)) = true := by quickRfl

theorem baseOKO : allN 4 (fun t => Nat.beq (ruBaseArr 4060 ruJoinBase)[t]!
    (pg 12 (mask 12) RuJO.BP t)) = true := by quickRfl

theorem permJ : allN 18 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuJS.S j) (RuJS.SI j)) =
    true := by quickRfl

theorem permO : allN 18 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (RuJO.S j) (RuJO.SI j)) =
    true := by quickRfl

theorem cnt0 : Nat.beq (rcnt (RuJO.LR 0)) 4060 = true := by quickRfl
theorem cnt1 : Nat.beq (rcnt (RuJO.LR 1)) 1755 = true := by quickRfl
theorem cnt2 : Nat.beq (rcnt (RuJO.LR 2)) 640 = true := by quickRfl
theorem cnt3 : Nat.beq (rcnt (RuJO.LR 3)) 32 = true := by quickRfl

theorem a0Hi : Nat.beq (Nat.shiftRight RuG.A0 (4060 * 12)) 0 = true := by quickRfl
theorem a1Hi : Nat.beq (Nat.shiftRight RuG.A1 (4060 * 12)) 0 = true := by quickRfl
theorem a0R : allN 4060 (fun i => Nat.blt (pg 12 (mask 12) RuG.A0 i) 4060) = true := by quickRfl
theorem a1R : allN 4060 (fun i => Nat.blt (pg 12 (mask 12) RuG.A1 i) 4060) = true := by quickRfl

theorem siftKA0 : siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0
    RuG.A0 = true := by quickRfl
theorem siftKA1 : siftK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) RuJS.LR RuJS.TRI RuJS.BP 4 0
    RuG.A1 = true := by quickRfl

theorem field_get {j : Nat} (hj : j < 18) : (ruField4060 3)[j]! = ruArr4060 (15 + j) := by
  rw [ruField4060, getElem!_pos _ j (by simpa [ruLines4060] using hj), Array.getElem_ofFn]
  rfl

theorem bindsJ : Binds 4060 12 RuJS.S 18 4 RuJS.BP (ruField4060 3) (ruBaseArr 4060 ruJoinBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [ruField4060, ruLines4060],
    fun j hj => by
      have e : RuJS.S j = RuT4060.L (15 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKJ j hj)
      rw [field_get hj, e]
      exact row4060 (by omega),
    by simp [ruBaseArr, ruJoinBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKJ t ht)⟩

theorem bindsO : Binds 4060 12 RuJO.S 18 4 RuJO.BP (ruField4060 3) (ruBaseArr 4060 ruJoinBase) :=
  ⟨by norm_num, by norm_num, by norm_num, by simp [ruField4060, ruLines4060],
    fun j hj => by
      have e : RuJO.S j = RuT4060.L (15 + j) := Nat.eq_of_beq_eq_true (allN_spec sOKO j hj)
      rw [field_get hj, e]
      exact row4060 (by omega),
    by simp [ruBaseArr, ruJoinBase], fun t ht => Nat.eq_of_beq_eq_true (allN_spec baseOKO t ht)⟩

theorem orbits : rawOrbitSizes 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase) =
    [4060, 1755, 640, 32] := by
  rw [rawOrbitSizesK_orb bindsO permO RuJO.ho (by norm_num)]
  simp [List.range_succ, Nat.eq_of_beq_eq_true cnt0, Nat.eq_of_beq_eq_true cnt1,
    Nat.eq_of_beq_eq_true cnt2, Nat.eq_of_beq_eq_true cnt3]

theorem basicAll : isInvA 4060 ruA0A (ruInv ruA0A) = true ∧ isInvA 4060 ruA1A (ruInv ruA1A) = true ∧
    ruCRunA.2.2 = true ∧ ruNRunA.2.2 = true ∧ isInvA 4060 ruN0A (ruInv ruN0A) = true ∧
    isInvA 4060 ruN1A (ruInv ruN1A) = true ∧ isInvA 4060 ruC0A (ruInv ruC0A) = true ∧
    isInvA 4060 ruC1A (ruInv ruC1A) = true ∧ isInvA 4060 ruWA (ruInv ruWA) = true ∧
    isInvA 4060 ruHA (ruInv ruHA) = true ∧ isInvA 4060 ruNs0A (ruInv ruNs0A) = true ∧
    isInvA 4060 ruNs1A (ruInv ruNs1A) = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := RuG.basic
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem rA0 : Rep 4060 ruA0A ruA0 := (rep_permOfArr basicAll.1).1
theorem rA1 : Rep 4060 ruA1A ruA1 := (rep_permOfArr basicAll.2.1).1
theorem rC0 : Rep 4060 ruC0A ruC0 := (rep_slotRunA ruCProg rA0 rA1 basicAll.2.2.1).1
theorem rC1 : Rep 4060 ruC1A ruC1 := (rep_slotRunA ruCProg rA0 rA1 basicAll.2.2.1).2
theorem rN0 : Rep 4060 ruN0A ruN0 := (rep_slotRunA ruNProg rA0 rA1 basicAll.2.2.2.1).1
theorem rN1 : Rep 4060 ruN1A ruN1 := (rep_slotRunA ruNProg rA0 rA1 basicAll.2.2.2.1).2
theorem rZ : Rep 4060 ruZA ruZ := rep_powA rC0 10

theorem rZ0 : Rep 4060 ruZ0A ruZ0 :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rN0 rN1)
    (rep_pair_getD_inv (rep_ruInv rN0 basicAll.2.2.2.2.1)
      (rep_ruInv rN1 basicAll.2.2.2.2.2.1)) _ (lettersK_sound Ru2247.l1)

theorem rW : Rep 4060 ruWA ruW :=
  rep_wordA_evalSigned (k := 2) (rep_pair_getD rA0 rA1)
    (rep_pair_getD_inv (rep_ruInv rA0 basicAll.1)
      (rep_ruInv rA1 basicAll.2.1)) _ (lettersK_sound Ru2247.l2)

theorem rU : Rep 4060 ruUA ruU :=
  rep_compA (rep_compA (rep_compA rW rZ0) (rep_ruInv rW basicAll.2.2.2.2.2.2.2.2.1)) rZ

theorem rH : Rep 4060 ruHA ruH := rep_compA (rep_powA rU 3) rW

theorem rNs0 : Rep 4060 ruNs0A ruNs0 :=
  rep_compA (rep_compA rH rN0) (rep_ruInv rH basicAll.2.2.2.2.2.2.2.2.2.1)

theorem rNs1 : Rep 4060 ruNs1A ruNs1 :=
  rep_compA (rep_compA rH rN1) (rep_ruInv rH basicAll.2.2.2.2.2.2.2.2.2.1)

theorem strong_inv {j : Nat} (hj : j < 18) :
    isInvA 4060 (ruField4060 3)[j]! (invCand 4060 (ruField4060 3)[j]!) = true :=
  isInv_of (bindsJ.2.2.2.2.1 j hj) (allN_spec permJ j hj)

theorem orig_mem {j : Nat} (hj : j < 4) : permOfArr 4060 (ruField4060 3)[j]! ∈ ruP := by
  have g := RuCe.facts.1
  interval_cases j
  · rw [permOfArr_eq_of_eqA (strong_inv (by omega)) rC0 g.2.2.2.2.1]
    exact ruC0_mem
  · rw [permOfArr_eq_of_eqA (strong_inv (by omega)) rC1 g.2.2.2.2.2.1]
    exact ruC1_mem
  · rw [permOfArr_eq_of_eqA (strong_inv (by omega)) rNs0 g.2.2.2.2.2.2.1]
    exact ruNs0_mem
  · rw [permOfArr_eq_of_eqA (strong_inv (by omega)) rNs1 g.2.2.2.2.2.2.2.1]
    exact ruNs1_mem

theorem card_le : Nat.card (Subgroup.closure (Set.range fun j : Fin 4 =>
    permOfArr 4060 (ruField4060 3)[j.val]!)) ≤
    (rawOrbitSizes 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase)).prod := by
  have hle : Subgroup.closure (Set.range fun j : Fin 4 => permOfArr 4060 (ruField4060 3)[j.val]!) ≤
      ruP := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact orig_mem j.2
  rw [orbits]
  exact (Subgroup.card_le_of_le hle).trans (RuPres.card_ruP_le.trans (by norm_num))

theorem chain : ruChainOK 4060 (ruField4060 3) 4 18 ruJoinBase ruJoinDerivations = true :=
  rawChainK_of_card_orb 4 bindsO RuJO.head RuJO.ho (by norm_num) card_le

theorem siftA0 : ruSift 4060 (ruField4060 3) ruJoinBase ruA0A = true :=
  siftK_soundR bindsJ permJ RuJS.hl RuG.a0_eq (Nat.eq_of_beq_eq_true a0Hi) a0R siftKA0

theorem siftA1 : ruSift 4060 (ruField4060 3) ruJoinBase ruA1A = true :=
  siftK_soundR bindsJ permJ RuJS.hl RuG.a1_eq (Nat.eq_of_beq_eq_true a1Hi) a1R siftKA1

end CertificateChecks.KernelSporSch.RuJ

end
