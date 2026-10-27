module

public import Certificates.Kernel.SporSch.Ly.BS18009
public import Certificates.Kernel.Misc.LyDihChecks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLyDih

open CFSG.KC.Ord CFSG.KD.OrdLy CFSG.KS.SporSch.LyM CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native

local notation "U" X:max => unpackL 111 12 1332 X

theorem bne0 {i : Nat} (h : ¬ i = 0) : Nat.beq i 0 = false := by
  cases i with
  | zero => exact absurd rfl h
  | succ n => rfl

theorem seedM_eq (i : Nat) : seedM i = U (GS i) := by
  unfold seedM GS
  by_cases h : i = 0
  · subst h
    exact matA_eq
  · rw [if_neg h, matB_eq, bne0 h]

theorem seedMInv_eq (i : Nat) : seedMInv (powM 5 111 matB 4) i = U (GSI i) := by
  unfold seedMInv GSI
  by_cases h : i = 0
  · subst h
    exact matA_eq
  · rw [if_neg h, b4_eq, bne0 h]

theorem vGS (i : Nat) : vld (GS i) = true := by
  unfold GS
  cases Nat.beq i 0
  · exact vB
  · exact vA

theorem vGSI (i : Nat) : vld (GSI i) = true := by
  unfold GSI
  cases Nat.beq i 0
  · exact vB4
  · exact vA

theorem wordE (w : List Int) :
    lySeedWordM w = U (wordR 5 12 1332 111 8 L H CM RM GS GSI ONE w) ∧
      vld (wordR 5 12 1332 111 8 L H CM RM GS GSI ONE w) = true :=
  word_of seedM_eq seedMInv_eq vGS vGSI w

theorem lyDihCheck_true : lyDihCheck () = true := by
  have hC : lyDihC () = U CW := (wordE lyDihWord).1
  have vC : vld CW = true := (wordE lyDihWord).2
  have hCi : lyDihCi () = U CWi := (wordE lyDihWordInv).1
  have vCi : vld CWi = true := (wordE lyDihWordInv).2
  have hP : lyDihP () = U PK := by
    unfold lyDihP PK
    rw [show lyDihC () = U CW from hC, show lyDihCi () = U CWi from hCi, matA_eq,
      mulE vC vA, mulE (mulV vC vA) vCi, mulE vA (mulV (mulV vC vA) vCi)]
  have vP : vld PK = true := mulV vA (mulV (mulV vC vA) vCi)
  have h := dih_ok
  unfold lyDihCheck
  rw [show lyDihC () = U CW from hC, show lyDihCi () = U CWi from hCi, hP, mulE vC vCi, idE,
    beqE (mulV vC vCi) vOne, (powM_eq consts (hv vP) 37).1,
    beqE (powM_eq consts (hv vP) 37).2 vOne, diffMod5_eq consts (hv vP) (hv vOne)]
  exact h

end CertificateChecks.KernelLyDih

end
