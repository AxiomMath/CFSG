module

public import Certificates.Kernel.SporSch.Tits.Stab2270K
public import Certificates.Kernel.SporSch.Tits.Prim2269T
public import Certificates.Kernel.SporSch.Tits.GenPrim
public import Certificates.Kernel.SporSch.Tits.Common
public import CFSG.Certificates.Kernel.MergeGSound
public import CFSG.Sporadic.Schreier.TitsPrimCheckInputs
meta import CFSG.Sporadic.Schreier.TitsData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public import CFSG.Sporadic.Schreier.Co1ThreeLocal

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSporSch.TitsPrim

meta def repsH : List Nat := [0, 1, 6, 24, 87]

end CertificateChecks.KernelSporSch.TitsPrim

#kst_stab CertificateChecks.KernelSporSch.TitsSD 1755 11 CertificateChecks.KernelMisc.TitsText.F
  CFSG.Sporadic.Schreier.Tits.titsDerivedDerivations CFSG.Sporadic.Schreier.Tits.titsDerivedComm
#kst_words CertificateChecks.KernelSporSch.TitsNW 2925 12
  CertificateChecks.KernelSporSch.TitsSS.T 13
  CFSG.Sporadic.Schreier.Tits.titsNWords
#kst_forest CertificateChecks.KernelSporSch.TitsFH 1755 11 CertificateChecks.KernelSpor.TitsD.S 2 11
  CertificateChecks.KernelSporSch.TitsPrim.repsH
#kst_forest CertificateChecks.KernelSporSch.TitsFN 2925 12
  CertificateChecks.KernelSporSch.TitsNW.W 0 4
  CFSG.Sporadic.Schreier.Tits.titsOtherReps
#kst_merge CertificateChecks.KernelSporSch.TitsMO 1755 11 CertificateChecks.KernelSporSch.TitsSD.T
  CFSG.Sporadic.Schreier.Tits.titsMergesText 0 1753 4 CFSG.Sporadic.Schreier.Tits.titsStabReps 0 32
#kst_merge CertificateChecks.KernelSporSch.TitsMS 2925 12 CertificateChecks.KernelSporSch.TitsSS.T
  CFSG.Sporadic.Schreier.Tits.titsMergesText 7012 2923 5 CFSG.Sporadic.Schreier.Tits.titsOtherReps 1
  32

namespace CertificateChecks.KernelSporSch.TitsPrim

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.MergeG
open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelMisc CertificateChecks.KernelSporSch

theorem dG : allN 4 (fun j => permW 1755 11 (TitsText.F j) (TitsSD.GI j)) = true := by quickRfl
theorem dU0u : wordW 1755 11 TitsText.F TitsSD.GI 4 (titsU 0) (TitsSD.U 0) = true := by quickRfl
theorem dU0v : wordW 1755 11 TitsText.F TitsSD.GI 4 (titsV 0) (TitsSD.V 0) = true := by quickRfl
theorem dU1u : wordW 1755 11 TitsText.F TitsSD.GI 4 (titsU 1) (TitsSD.U 1) = true := by quickRfl
theorem dU1v : wordW 1755 11 TitsText.F TitsSD.GI 4 (titsV 1) (TitsSD.V 1) = true := by quickRfl
theorem dUp : allN 2 (fun j => bAnd(permW 1755 11 (TitsSD.U j) (TitsSD.UI j),
    permW 1755 11 (TitsSD.V j) (TitsSD.VI j))) = true := by quickRfl
theorem dC : allN 2 (fun j => bAnd(eq2W 1755 11 (TitsSD.A j) (TitsSD.UI j) (TitsSD.VI j),
    bAnd(eq2W 1755 11 (TitsSD.B j) (TitsSD.A j) (TitsSD.U j),
    eq2W 1755 11 (TitsSD.T j) (TitsSD.B j) (TitsSD.V j)))) = true := by quickRfl
theorem dCan : allN 2 (fun i => canonK 1755 11 (mask 11) (1755 * 11) (TitsSD.T i)) = true := by
  quickRfl

theorem kH0 : ((List.range 13).filter fun j => Nat.beq (pg 11 (mask 11) (TitsD.S j) 0) 0) =
    [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] := by decide
theorem hCan : allN 11 (fun i => canonK 1755 11 (mask 11) (1755 * 11) (TitsD.S (Nat.add i 2))) =
    true := by quickRfl
theorem nW0 : wordW 2925 12 TitsSS.T TitsSS.TI 13 titsNWords[0]! (TitsNW.W 0) = true := by quickRfl
theorem nW1 : wordW 2925 12 TitsSS.T TitsSS.TI 13 titsNWords[1]! (TitsNW.W 1) = true := by quickRfl
theorem nW2 : wordW 2925 12 TitsSS.T TitsSS.TI 13 titsNWords[2]! (TitsNW.W 2) = true := by quickRfl
theorem nW3 : wordW 2925 12 TitsSS.T TitsSS.TI 13 titsNWords[3]! (TitsNW.W 3) = true := by quickRfl
theorem nCan : allN 4 (fun i => canonK 2925 12 (mask 12) (2925 * 12) (TitsNW.W i)) = true := by
  quickRfl

theorem fH : bfsTK 1755 11 (fun i => TitsD.S (Nat.add i 2)) 11 5 TitsFH.REP TitsFH.N TitsFH.Q
    TitsFH.POS TitsFH.C TitsFH.LAB TitsFH.DEP TitsFH.PAR TitsFH.GL = true := by quickRfl
theorem lH : labOKK 1755 11 (fun i => TitsD.S (Nat.add i 2)) 11 5 TitsFH.LAB TitsFH.REP TitsFH.DEP
    TitsFH.PAR TitsFH.GL = true := by quickRfl
theorem cH : (List.range 5).map (cntK 1755 11 TitsFH.LAB) = [1, 10, 80, 640, 1024] := by decide
theorem rH : allN 1755 (fun x => Nat.ble (pgW 11 TitsFH.REP (pgW 11 TitsFH.LAB x)) x) = true := by
  quickRfl
theorem rH0 : Nat.beq (Nat.shiftRight TitsFH.REP (5 * 11)) 0 = true := by quickRfl
theorem rHe : (#[0, 1, 6, 24, 87] : Array Nat) = unpack 5 11 TitsFH.REP := by decide

theorem fN : bfsTK 2925 12 TitsNW.W 4 6 TitsFN.REP TitsFN.N TitsFN.Q TitsFN.POS TitsFN.C TitsFN.LAB
    TitsFN.DEP TitsFN.PAR TitsFN.GL = true := by quickRfl
theorem lN : labOKK 2925 12 TitsNW.W 4 6 TitsFN.LAB TitsFN.REP TitsFN.DEP TitsFN.PAR TitsFN.GL =
    true := by quickRfl
theorem cN : (List.range 6).map (cntK 2925 12 TitsFN.LAB) = [1, 12, 96, 768, 1024, 1024] := by
  decide
theorem rN : allN 2925 (fun x => Nat.ble (pgW 12 TitsFN.REP (pgW 12 TitsFN.LAB x)) x) = true := by
  quickRfl
theorem rN0 : Nat.beq (Nat.shiftRight TitsFN.REP (6 * 12)) 0 = true := by quickRfl
theorem rNe : (#[0, 1, 7, 27, 107, 141] : Array Nat) = unpack 6 12 TitsFN.REP := by decide

theorem kMg : CFSG.KC.Misc.HexFlat.hexFlat TitsMg.chars 1 623 4 243 TitsMg.F = true := TitsMg.all

@[expose] noncomputable def recI (K0 k : Nat) : Nat := Nat.mod (digK TitsMg.F (7 * (K0 + k))) 2

@[expose] noncomputable def recU (n K0 k : Nat) : Nat :=
  Nat.mod (hex3K TitsMg.F (Nat.add (7 * (K0 + k)) 1)) n

@[expose] noncomputable def recV (n K0 k : Nat) : Nat :=
  Nat.mod (hex3K TitsMg.F (Nat.add (7 * (K0 + k)) 4)) n

theorem allN_chunks {f : Nat → Bool} {B C n : Nat} (hn : n ≤ B * C)
    (h : ∀ c < C, allN B (fun t => bIf(Nat.blt (B * c + t) n, f (B * c + t), true)) = true) :
    allN n f = true := by
  refine allN_of_forall fun s hs => ?_
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0, Nat.zero_mul] at hn
      omega
    · exact h0
  have hc : s / B < C := by
    rw [Nat.div_lt_iff_lt_mul hB]
    rw [Nat.mul_comm] at hn
    omega
  have h1 := allN_spec (h (s / B) hc) (s % B) (Nat.mod_lt _ hB)
  rw [Nat.div_add_mod] at h1
  have h2 : Nat.blt s n = true := by rw [Nat.blt_eq]; exact hs
  rw [h2] at h1
  exact h1

theorem mergeCKG_of {n w kG b x Lc S NS TP PP : Nat} {GS RI RU RV A : Nat → Nat}
    (h0 : bAnd(Nat.blt b n, bAnd(Nat.blt x n, bAnd(Nat.blt Lc 4096, bAnd(Nat.blt 0 S,
      Nat.ble Lc (Nat.mul S NS))))) = true)
    (hA : allN n (fun y => Nat.beq (pgW w (A 0) y) (nIf(Nat.beq y x, b, y))) = true)
    (hs : allN NS (segCG n w kG GS Lc S TP PP A RI RU RV) = true)
    (hT : allN n (fun l => Nat.ble (pgW 12 TP l) Lc) = true)
    (hc : Nat.beq (mergeCnt n w GS Lc S TP PP A RI RU RV) (timedCnt n Lc TP) = true)
    (hf : finalC n w Lc NS TP A = true) :
    mergeCKG n w kG GS b x Lc S NS RI RU RV TP PP A = true := by
  obtain ⟨e1, r1⟩ := (bAnd_iff _ _).1 h0
  obtain ⟨e2, r2⟩ := (bAnd_iff _ _).1 r1
  obtain ⟨e3, r3⟩ := (bAnd_iff _ _).1 r2
  obtain ⟨e4, e5⟩ := (bAnd_iff _ _).1 r3
  unfold mergeCKG
  rw [e1, e2, e3, e4, e5, hA, hs, hT, hc, hf]

theorem sCan : allN 2 (fun i => canonK 2925 12 (mask 12) (2925 * 12) (TitsSS.T i)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.TitsPrim

end
