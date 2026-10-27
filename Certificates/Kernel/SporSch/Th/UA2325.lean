
module

public import Certificates.Kernel.SporSch.Th.Cent
public import Certificates.Kernel.SporSch.Th.Row2322
public import CFSG.Sporadic.ThSchreier.UASpaceInputs
meta import CFSG.Sporadic.ThSchreier.UASpaceInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelSporSch.ThUAT CFSG.Sporadic.ThSchreier.uaRowsTxt
#ks_chars CertificateChecks.KernelSporSch.ThSeedA CFSG.Sporadic.Th.Native.seedA
#kss_v4rows CertificateChecks.KernelSporSch.ThA CFSG.Sporadic.Th.Max3.rowsA
#kss_natlist CertificateChecks.KernelSporSch.ThU CFSG.Sporadic.ThSchreier.uaRowsTxt

namespace CertificateChecks.KernelSporSch.ThUA

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1 lt_of)
open CertificateChecks.KernelSporSch.ThCent (scan0 NV)

@[expose] noncomputable def UB (k i : Nat) : Nat := ThU (Nat.add (Nat.mul 248 k) i)

@[expose] noncomputable def AMI (i : Nat) : Nat := Nat.xor (ThA i) (Nat.shiftLeft 1 i)

meta def paArr : Array V4 := mulRows rowsUAP rowsAmI

end CertificateChecks.KernelSporSch.ThUA

#kss_v4rows CertificateChecks.KernelSporSch.ThPA CertificateChecks.KernelSporSch.ThUA.paArr

namespace CertificateChecks.KernelSporSch.ThUA

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1 lt_of)
open CertificateChecks.KernelSporSch.ThCent (scan0 NV)

@[expose] noncomputable def D120 (i : Nat) : Nat := nIf(Nat.blt i 120, Nat.shiftLeft 1 i, 0)

theorem seedA_ok : thPayK ThA ThSeedA.chars = true := by quickRfl
theorem bindU : Nat.beq (thBindK true ThU ThUAT.chars) (2 * 992) = true := by quickRfl
theorem scanU : Nat.beq (thScanK true (2 ^ 248) NV ThUAT.chars) (4 * 992) = true := by quickRfl

theorem ltA : allN 248 (fun i => Nat.blt (ThA i) (Nat.shiftLeft 1 248)) = true := by quickRfl
theorem ltAMI : allN 248 (fun i => Nat.blt (AMI i) (Nat.shiftLeft 1 248)) = true := by quickRfl
theorem ltPA : allN 248 (fun i => Nat.blt (ThPA i) (Nat.shiftLeft 1 248)) = true := by quickRfl
theorem ltU : allN 992 (fun i => Nat.blt (ThU i) (Nat.shiftLeft 1 248)) = true := by quickRfl

theorem all8 {f : Nat → Bool} (h0 : allBlk 0 f 31 = true) (h1 : allBlk 31 f 31 = true)
    (h2 : allBlk 62 f 31 = true) (h3 : allBlk 93 f 31 = true) (h4 : allBlk 124 f 31 = true)
    (h5 : allBlk 155 f 31 = true) (h6 : allBlk 186 f 31 = true) (h7 : allBlk 217 f 31 = true) :
    ∀ i < 248, f i = true := by
  intro i hi
  have key : ∀ (b : Nat), allBlk b f 31 = true → b ≤ i → i < b + 31 → f i = true := by
    intro b hb h1' h2'
    have := allBlk_spec hb (i - b) (by omega)
    rwa [Nat.add_eq, Nat.add_sub_cancel' h1'] at this
  rcases Nat.lt_or_ge i 31 with a | a
  · exact key 0 h0 (by omega) (by omega)
  rcases Nat.lt_or_ge i 62 with b | b
  · exact key 31 h1 a (by omega)
  rcases Nat.lt_or_ge i 93 with c | c
  · exact key 62 h2 b (by omega)
  rcases Nat.lt_or_ge i 124 with d | d
  · exact key 93 h3 c (by omega)
  rcases Nat.lt_or_ge i 155 with e | e
  · exact key 124 h4 d (by omega)
  rcases Nat.lt_or_ge i 186 with f | f
  · exact key 155 h5 e (by omega)
  rcases Nat.lt_or_ge i 217 with g | g
  · exact key 186 h6 f (by omega)
  · exact key 217 h7 g (by omega)

@[expose] noncomputable def fPA (i : Nat) : Bool := Nat.beq (vmT AMI (UB 0 i)) (ThPA i)
@[expose] noncomputable def fD (i : Nat) : Bool := Nat.beq (vmT (UB 1) (ThPA i)) (D120 i)
@[expose] noncomputable def fP (i : Nat) : Bool := Nat.beq (vmT (UB 0) (UB 2 i)) (Nat.shiftLeft 1 i)
@[expose] noncomputable def fQ (i : Nat) : Bool := Nat.beq (vmT (UB 3) (UB 1 i)) (Nat.shiftLeft 1 i)

theorem pa0 : allBlk 0 fPA 31 = true := by quickRfl
theorem pa1 : allBlk 31 fPA 31 = true := by quickRfl
theorem pa2 : allBlk 62 fPA 31 = true := by quickRfl
theorem pa3 : allBlk 93 fPA 31 = true := by quickRfl
theorem pa4 : allBlk 124 fPA 31 = true := by quickRfl
theorem pa5 : allBlk 155 fPA 31 = true := by quickRfl
theorem pa6 : allBlk 186 fPA 31 = true := by quickRfl
theorem pa7 : allBlk 217 fPA 31 = true := by quickRfl
theorem d0 : allBlk 0 fD 31 = true := by quickRfl
theorem d1 : allBlk 31 fD 31 = true := by quickRfl
theorem d2 : allBlk 62 fD 31 = true := by quickRfl
theorem d3 : allBlk 93 fD 31 = true := by quickRfl
theorem d4 : allBlk 124 fD 31 = true := by quickRfl
theorem d5 : allBlk 155 fD 31 = true := by quickRfl
theorem d6 : allBlk 186 fD 31 = true := by quickRfl
theorem d7 : allBlk 217 fD 31 = true := by quickRfl
theorem p0 : allBlk 0 fP 31 = true := by quickRfl
theorem p1 : allBlk 31 fP 31 = true := by quickRfl
theorem p2 : allBlk 62 fP 31 = true := by quickRfl
theorem p3 : allBlk 93 fP 31 = true := by quickRfl
theorem p4 : allBlk 124 fP 31 = true := by quickRfl
theorem p5 : allBlk 155 fP 31 = true := by quickRfl
theorem p6 : allBlk 186 fP 31 = true := by quickRfl
theorem p7 : allBlk 217 fP 31 = true := by quickRfl
theorem q0 : allBlk 0 fQ 31 = true := by quickRfl
theorem q1 : allBlk 31 fQ 31 = true := by quickRfl
theorem q2 : allBlk 62 fQ 31 = true := by quickRfl
theorem q3 : allBlk 93 fQ 31 = true := by quickRfl
theorem q4 : allBlk 124 fQ 31 = true := by quickRfl
theorem q5 : allBlk 155 fQ 31 = true := by quickRfl
theorem q6 : allBlk 186 fQ 31 = true := by quickRfl
theorem q7 : allBlk 217 fQ 31 = true := by quickRfl

theorem ltUB (k : Nat) (hk : k < 4) : ∀ i < 248, UB k i < 2 ^ 248 := fun i hi => by
  have := Nat.blt_eq.mp (allN_spec ltU (248 * k + i) (by omega))
  rwa [sh1] at this

theorem block_eq (k : Nat) (hk : k < 4) : uaBlock k = rowsV (UB k) := by
  have hb := Nat.eq_of_beq_eq_true bindU
  obtain ⟨hl0, hv0⟩ := thBind_sound (hex := true) (R := ThU) (cs := ThUAT.chars) (by rw [hb])
  have hl : (hexsOf (String.ofList ThUAT.chars)).length = thBindK true ThU ThUAT.chars / 2 := hl0
  have hv : ∀ t < (hexsOf (String.ofList ThUAT.chars)).length,
      (hexsOf (String.ofList ThUAT.chars)).getD t 0 = ThU t := hv0
  rw [hb] at hl
  rw [uaBlock, ThUAT.eq, rowsV]
  congr 1
  funext i
  have := i.isLt
  rw [hv _ (by rw [hl]; omega)]
  rfl

theorem rowsA_eq : CFSG.Sporadic.Th.Max3.rowsA = rowsV ThA := by
  rw [CFSG.Sporadic.Th.Max3.rowsA, ThSeedA.eq]
  exact thPay_sound seedA_ok

theorem un {f : Nat → Bool} {g : Nat → Nat} {h : Nat → Nat} (hf : ∀ i, f i = Nat.beq (g i) (h i))
    (H : ∀ i < 248, f i = true) : ∀ i < 248, g i = h i :=
  fun i hi => Nat.eq_of_beq_eq_true ((hf i).symm.trans (H i hi))

theorem facts : eqRows (mulRows (mulRows rowsUAP rowsAmI) rowsUAQ) rowsD120 = true ∧
    eqRows (mulRows rowsUAPInv rowsUAP) idRows = true ∧
    eqRows (mulRows rowsUAQ rowsUAQInv) idRows = true ∧
    (∀ n ∈ uaRowsTxt, n < 2 ^ 248) ∧ uaRowsTxt.length = 4 * 248 := by
  have bP := ltUB 0 (by omega)
  have bQ := ltUB 1 (by omega)
  have bPI := ltUB 2 (by omega)
  have bQI := ltUB 3 (by omega)
  have bA : ∀ i < 248, ThA i < 2 ^ 248 := fun i hi => by
    have := Nat.blt_eq.mp (allN_spec ltA i hi)
    rwa [sh1] at this
  have bAMI : ∀ i < 248, AMI i < 2 ^ 248 := fun i hi => by
    have := Nat.blt_eq.mp (allN_spec ltAMI i hi)
    rwa [sh1] at this
  have bPA : ∀ i < 248, ThPA i < 2 ^ 248 := fun i hi => by
    have := Nat.blt_eq.mp (allN_spec ltPA i hi)
    rwa [sh1] at this
  have hAMI : rowsAmI = rowsV AMI := by
    rw [rowsAmI_sound rowsA_eq bA]
    congr 1
    funext i
    rw [AMI, sh1]
  have hPA : mulRows rowsUAP rowsAmI = rowsV ThPA := by
    rw [rowsUAP, block_eq 0 (by omega), hAMI]
    exact mulRows_sound bP bAMI (un (fun _ => rfl) (all8 pa0 pa1 pa2 pa3 pa4 pa5 pa6 pa7))
  have hD : ∀ i < 248, vmT (UB 1) (ThPA i) = if i < 120 then 2 ^ i else 0 := by
    intro i hi
    rw [un (g := fun i => vmT (UB 1) (ThPA i)) (h := D120) (fun _ => rfl)
      (all8 d0 d1 d2 d3 d4 d5 d6 d7) i hi, D120]
    by_cases hc : i < 120
    · simp only [hc, ↓reduceIte]
      rw [Nat.blt_eq.mpr hc, sh1]
    · simp only [hc, ↓reduceIte]
      have : Nat.blt i 120 = false := Bool.eq_false_iff.mpr fun h' => hc (Nat.blt_eq.mp h')
      rw [this]
  have hP : ∀ i < 248, vmT (UB 0) (UB 2 i) = 2 ^ i := fun i hi => by
    rw [un (g := fun i => vmT (UB 0) (UB 2 i)) (h := fun i => Nat.shiftLeft 1 i) (fun _ => rfl)
      (all8 p0 p1 p2 p3 p4 p5 p6 p7) i hi, sh1]
  have hQ : ∀ i < 248, vmT (UB 3) (UB 1 i) = 2 ^ i := fun i hi => by
    rw [un (g := fun i => vmT (UB 3) (UB 1 i)) (h := fun i => Nat.shiftLeft 1 i) (fun _ => rfl)
      (all8 q0 q1 q2 q3 q4 q5 q6 q7) i hi, sh1]
  have hs := scan0 scanU
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hPA, rowsUAQ, block_eq 1 (by omega)]
    exact mulD120_sound bPA bQ hD
  · rw [rowsUAPInv, rowsUAP, block_eq 2 (by omega), block_eq 0 (by omega)]
    exact mulId_sound bPI bP hP
  · rw [rowsUAQ, rowsUAQInv, block_eq 1 (by omega), block_eq 3 (by omega)]
    exact mulId_sound bQ bQI hQ
  · rw [ThUAT.eq]
    exact hs.2
  · rw [ThUAT.eq]
    exact hs.1

end CertificateChecks.KernelSporSch.ThUA

end
