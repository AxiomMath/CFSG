module

public import Certificates.Kernel.Misc.Perm.J5G
public import CFSG.Certificates.Kernel.Misc.ArrEnumUnpack
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelMisc.CertBind (Bound cert_facts)
open CFSG.KC.Misc.Clos (allN_iff allR forall_of_chunks)

@[expose] noncomputable def keyF (F : ℕ → ℕ) (i : ℕ) : Bool :=
  CFSG.KC.LQT.P.allN i fun j => !(Nat.beq (keyK 315 9 j2FiveKeyPts (F i))
    (keyK 315 9 j2FiveKeyPts (F j)))

theorem keys_of_all {N : ℕ} {F : ℕ → ℕ} (h : ∀ i < N, keyF F i = true) :
    ∀ i < N, ∀ j < i, keyK 315 9 j2FiveKeyPts (F i) ≠ keyK 315 9 j2FiveKeyPts (F j) := by
  intro i hi j hj he
  have h2 := (allN_iff _ _).1 (h i hi) j hj
  rw [he, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

@[expose] noncomputable def EF (FE : ℕ → ℕ) (i k : ℕ) : ℕ := pg 12 (mask 12) (FE i) k

@[expose] noncomputable def VF (FR : ℕ → ℕ) (i : ℕ) : ℕ := pg 12 (mask 12) (FR 0) i

theorem ptQ_0 : allR 0 25
    (pointK 315 9 2 25 QG QP.F (EF QE.F) (VF QR.F) (VF QL.F)) = true := by quickRfl
theorem ptQ_All : ∀ i < 25,
    (pointK 315 9 2 25 QG QP.F (EF QE.F) (VF QR.F) (VF QL.F)) i = true :=
  forall_of_chunks 25 1 _ fun c hc => by
    interval_cases c
    · exact ptQ_0

theorem kyQ_0 : allR 0 25
    (keyF QP.F) = true := by quickRfl
theorem kyQ_All : ∀ i < 25,
    (keyF QP.F) i = true :=
  forall_of_chunks 25 1 _ fun c hc => by
    interval_cases c
    · exact kyQ_0

theorem enumQ : enumOK 315 j2FiveQGenArrs j2FiveKeyPts j2FiveQCert = true :=
  enumK_sound' (G := QG) hw (by decide) (by decide) hQGA bQ.1 bQ.2.1 bQ.2.2.1
    (fun i hi => bQ.2.2.2 i hi) (by quickRfl) ptQ_All (keys_of_all kyQ_All)

theorem ptC0_0 : allR 0 25
    (pointK 315 9 2 50 CGP0 C0P.F (EF C0E.F) (VF C0R.F) (VF C0L.F)) = true := by quickRfl
theorem ptC0_1 : allR 25 25
    (pointK 315 9 2 50 CGP0 C0P.F (EF C0E.F) (VF C0R.F) (VF C0L.F)) = true := by quickRfl
theorem ptC0_All : ∀ i < 50,
    (pointK 315 9 2 50 CGP0 C0P.F (EF C0E.F) (VF C0R.F) (VF C0L.F)) i = true :=
  forall_of_chunks 25 2 _ fun c hc => by
    interval_cases c
    · exact ptC0_0
    · exact ptC0_1

theorem kyC0_0 : allR 0 25
    (keyF C0P.F) = true := by quickRfl
theorem kyC0_1 : allR 25 25
    (keyF C0P.F) = true := by quickRfl
theorem kyC0_All : ∀ i < 50,
    (keyF C0P.F) i = true :=
  forall_of_chunks 25 2 _ fun c hc => by
    interval_cases c
    · exact kyC0_0
    · exact kyC0_1

theorem enumC0 : enumOK 315 (j2FiveCG 0) j2FiveKeyPts (j2FiveCCert 0) = true :=
  enumK_sound' (G := CGP0) hw (by decide) (by decide) hCG0 bC0.1 bC0.2.1 bC0.2.2.1
    (fun i hi => bC0.2.2.2 i hi) (by quickRfl) ptC0_All (keys_of_all kyC0_All)

theorem ptC1_0 : allR 0 25
    (pointK 315 9 2 50 CGP1 C1P.F (EF C1E.F) (VF C1R.F) (VF C1L.F)) = true := by quickRfl
theorem ptC1_1 : allR 25 25
    (pointK 315 9 2 50 CGP1 C1P.F (EF C1E.F) (VF C1R.F) (VF C1L.F)) = true := by quickRfl
theorem ptC1_All : ∀ i < 50,
    (pointK 315 9 2 50 CGP1 C1P.F (EF C1E.F) (VF C1R.F) (VF C1L.F)) i = true :=
  forall_of_chunks 25 2 _ fun c hc => by
    interval_cases c
    · exact ptC1_0
    · exact ptC1_1

theorem kyC1_0 : allR 0 25
    (keyF C1P.F) = true := by quickRfl
theorem kyC1_1 : allR 25 25
    (keyF C1P.F) = true := by quickRfl
theorem kyC1_All : ∀ i < 50,
    (keyF C1P.F) i = true :=
  forall_of_chunks 25 2 _ fun c hc => by
    interval_cases c
    · exact kyC1_0
    · exact kyC1_1

theorem enumC1 : enumOK 315 (j2FiveCG 1) j2FiveKeyPts (j2FiveCCert 1) = true :=
  enumK_sound' (G := CGP1) hw (by decide) (by decide) hCG1 bC1.1 bC1.2.1 bC1.2.2.1
    (fun i hi => bC1.2.2.2 i hi) (by quickRfl) ptC1_All (keys_of_all kyC1_All)

theorem ptC2_0 : allR 0 50
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) = true := by quickRfl
theorem ptC2_1 : allR 50 50
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) = true := by quickRfl
theorem ptC2_2 : allR 100 50
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) = true := by quickRfl
theorem ptC2_3 : allR 150 50
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) = true := by quickRfl
theorem ptC2_4 : allR 200 50
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) = true := by quickRfl
theorem ptC2_5 : allR 250 50
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) = true := by quickRfl
theorem ptC2_All : ∀ i < 300,
    (pointK 315 9 3 300 CGP2 C2P.F (EF C2E.F) (VF C2R.F) (VF C2L.F)) i = true :=
  forall_of_chunks 50 6 _ fun c hc => by
    interval_cases c
    · exact ptC2_0
    · exact ptC2_1
    · exact ptC2_2
    · exact ptC2_3
    · exact ptC2_4
    · exact ptC2_5

theorem kyC2_0 : allR 0 50
    (keyF C2P.F) = true := by quickRfl
theorem kyC2_1 : allR 50 50
    (keyF C2P.F) = true := by quickRfl
theorem kyC2_2 : allR 100 50
    (keyF C2P.F) = true := by quickRfl
theorem kyC2_3 : allR 150 50
    (keyF C2P.F) = true := by quickRfl
theorem kyC2_4 : allR 200 50
    (keyF C2P.F) = true := by quickRfl
theorem kyC2_5 : allR 250 50
    (keyF C2P.F) = true := by quickRfl
theorem kyC2_All : ∀ i < 300,
    (keyF C2P.F) i = true :=
  forall_of_chunks 50 6 _ fun c hc => by
    interval_cases c
    · exact kyC2_0
    · exact kyC2_1
    · exact kyC2_2
    · exact kyC2_3
    · exact kyC2_4
    · exact kyC2_5

theorem enumC2 : enumOK 315 (j2FiveCG 2) j2FiveKeyPts (j2FiveCCert 2) = true :=
  enumK_sound' (G := CGP2) hw (by decide) (by decide) hCG2 bC2.1 bC2.2.1 bC2.2.2.1
    (fun i hi => bC2.2.2.2 i hi) (by quickRfl) ptC2_All (keys_of_all kyC2_All)

theorem ptC3_0 : allR 0 50
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) = true := by quickRfl
theorem ptC3_1 : allR 50 50
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) = true := by quickRfl
theorem ptC3_2 : allR 100 50
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) = true := by quickRfl
theorem ptC3_3 : allR 150 50
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) = true := by quickRfl
theorem ptC3_4 : allR 200 50
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) = true := by quickRfl
theorem ptC3_5 : allR 250 50
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) = true := by quickRfl
theorem ptC3_All : ∀ i < 300,
    (pointK 315 9 2 300 CGP3 C3P.F (EF C3E.F) (VF C3R.F) (VF C3L.F)) i = true :=
  forall_of_chunks 50 6 _ fun c hc => by
    interval_cases c
    · exact ptC3_0
    · exact ptC3_1
    · exact ptC3_2
    · exact ptC3_3
    · exact ptC3_4
    · exact ptC3_5

theorem kyC3_0 : allR 0 50
    (keyF C3P.F) = true := by quickRfl
theorem kyC3_1 : allR 50 50
    (keyF C3P.F) = true := by quickRfl
theorem kyC3_2 : allR 100 50
    (keyF C3P.F) = true := by quickRfl
theorem kyC3_3 : allR 150 50
    (keyF C3P.F) = true := by quickRfl
theorem kyC3_4 : allR 200 50
    (keyF C3P.F) = true := by quickRfl
theorem kyC3_5 : allR 250 50
    (keyF C3P.F) = true := by quickRfl
theorem kyC3_All : ∀ i < 300,
    (keyF C3P.F) i = true :=
  forall_of_chunks 50 6 _ fun c hc => by
    interval_cases c
    · exact kyC3_0
    · exact kyC3_1
    · exact kyC3_2
    · exact kyC3_3
    · exact kyC3_4
    · exact kyC3_5

theorem enumC3 : enumOK 315 (j2FiveCG 3) j2FiveKeyPts (j2FiveCCert 3) = true :=
  enumK_sound' (G := CGP3) hw (by decide) (by decide) hCG3 bC3.1 bC3.2.1 bC3.2.2.1
    (fun i hi => bC3.2.2.2 i hi) (by quickRfl) ptC3_All (keys_of_all kyC3_All)

theorem ptC4_0 : allR 0 25
    (pointK 315 9 3 50 CGP4 C4P.F (EF C4E.F) (VF C4R.F) (VF C4L.F)) = true := by quickRfl
theorem ptC4_1 : allR 25 25
    (pointK 315 9 3 50 CGP4 C4P.F (EF C4E.F) (VF C4R.F) (VF C4L.F)) = true := by quickRfl
theorem ptC4_All : ∀ i < 50,
    (pointK 315 9 3 50 CGP4 C4P.F (EF C4E.F) (VF C4R.F) (VF C4L.F)) i = true :=
  forall_of_chunks 25 2 _ fun c hc => by
    interval_cases c
    · exact ptC4_0
    · exact ptC4_1

theorem kyC4_0 : allR 0 25
    (keyF C4P.F) = true := by quickRfl
theorem kyC4_1 : allR 25 25
    (keyF C4P.F) = true := by quickRfl
theorem kyC4_All : ∀ i < 50,
    (keyF C4P.F) i = true :=
  forall_of_chunks 25 2 _ fun c hc => by
    interval_cases c
    · exact kyC4_0
    · exact kyC4_1

theorem enumC4 : enumOK 315 (j2FiveCG 4) j2FiveKeyPts (j2FiveCCert 4) = true :=
  enumK_sound' (G := CGP4) hw (by decide) (by decide) hCG4 bC4.1 bC4.2.1 bC4.2.2.1
    (fun i hi => bC4.2.2.2 i hi) (by quickRfl) ptC4_All (keys_of_all kyC4_All)

theorem ptC5_0 : allR 0 50
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) = true := by quickRfl
theorem ptC5_1 : allR 50 50
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) = true := by quickRfl
theorem ptC5_2 : allR 100 50
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) = true := by quickRfl
theorem ptC5_3 : allR 150 50
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) = true := by quickRfl
theorem ptC5_4 : allR 200 50
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) = true := by quickRfl
theorem ptC5_5 : allR 250 50
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) = true := by quickRfl
theorem ptC5_All : ∀ i < 300,
    (pointK 315 9 3 300 CGP5 C5P.F (EF C5E.F) (VF C5R.F) (VF C5L.F)) i = true :=
  forall_of_chunks 50 6 _ fun c hc => by
    interval_cases c
    · exact ptC5_0
    · exact ptC5_1
    · exact ptC5_2
    · exact ptC5_3
    · exact ptC5_4
    · exact ptC5_5

theorem kyC5_0 : allR 0 50
    (keyF C5P.F) = true := by quickRfl
theorem kyC5_1 : allR 50 50
    (keyF C5P.F) = true := by quickRfl
theorem kyC5_2 : allR 100 50
    (keyF C5P.F) = true := by quickRfl
theorem kyC5_3 : allR 150 50
    (keyF C5P.F) = true := by quickRfl
theorem kyC5_4 : allR 200 50
    (keyF C5P.F) = true := by quickRfl
theorem kyC5_5 : allR 250 50
    (keyF C5P.F) = true := by quickRfl
theorem kyC5_All : ∀ i < 300,
    (keyF C5P.F) i = true :=
  forall_of_chunks 50 6 _ fun c hc => by
    interval_cases c
    · exact kyC5_0
    · exact kyC5_1
    · exact kyC5_2
    · exact kyC5_3
    · exact kyC5_4
    · exact kyC5_5

theorem enumC5 : enumOK 315 (j2FiveCG 5) j2FiveKeyPts (j2FiveCCert 5) = true :=
  enumK_sound' (G := CGP5) hw (by decide) (by decide) hCG5 bC5.1 bC5.2.1 bC5.2.2.1
    (fun i hi => bC5.2.2.2 i hi) (by quickRfl) ptC5_All (keys_of_all kyC5_All)

theorem ptD2_0 : allR 0 30
    (pointK 315 9 3 60 DGP2 D2P.F (EF D2E.F) (VF D2R.F) (VF D2L.F)) = true := by quickRfl
theorem ptD2_1 : allR 30 30
    (pointK 315 9 3 60 DGP2 D2P.F (EF D2E.F) (VF D2R.F) (VF D2L.F)) = true := by quickRfl
theorem ptD2_All : ∀ i < 60,
    (pointK 315 9 3 60 DGP2 D2P.F (EF D2E.F) (VF D2R.F) (VF D2L.F)) i = true :=
  forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact ptD2_0
    · exact ptD2_1

theorem kyD2_0 : allR 0 30
    (keyF D2P.F) = true := by quickRfl
theorem kyD2_1 : allR 30 30
    (keyF D2P.F) = true := by quickRfl
theorem kyD2_All : ∀ i < 60,
    (keyF D2P.F) i = true :=
  forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact kyD2_0
    · exact kyD2_1

theorem enumD2 : enumOK 315 (j2FiveDG 2) j2FiveKeyPts (j2FiveDCert 2) = true :=
  enumK_sound' (G := DGP2) hw (by decide) (by decide) hDG2 bD2.1 bD2.2.1 bD2.2.2.1
    (fun i hi => bD2.2.2.2 i hi) (by quickRfl) ptD2_All (keys_of_all kyD2_All)

theorem ptD3_0 : allR 0 30
    (pointK 315 9 2 60 DGP3 D3P.F (EF D3E.F) (VF D3R.F) (VF D3L.F)) = true := by quickRfl
theorem ptD3_1 : allR 30 30
    (pointK 315 9 2 60 DGP3 D3P.F (EF D3E.F) (VF D3R.F) (VF D3L.F)) = true := by quickRfl
theorem ptD3_All : ∀ i < 60,
    (pointK 315 9 2 60 DGP3 D3P.F (EF D3E.F) (VF D3R.F) (VF D3L.F)) i = true :=
  forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact ptD3_0
    · exact ptD3_1

theorem kyD3_0 : allR 0 30
    (keyF D3P.F) = true := by quickRfl
theorem kyD3_1 : allR 30 30
    (keyF D3P.F) = true := by quickRfl
theorem kyD3_All : ∀ i < 60,
    (keyF D3P.F) i = true :=
  forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact kyD3_0
    · exact kyD3_1

theorem enumD3 : enumOK 315 (j2FiveDG 3) j2FiveKeyPts (j2FiveDCert 3) = true :=
  enumK_sound' (G := DGP3) hw (by decide) (by decide) hDG3 bD3.1 bD3.2.1 bD3.2.2.1
    (fun i hi => bD3.2.2.2 i hi) (by quickRfl) ptD3_All (keys_of_all kyD3_All)

theorem ptD5_0 : allR 0 30
    (pointK 315 9 2 60 DGP5 D5P.F (EF D5E.F) (VF D5R.F) (VF D5L.F)) = true := by quickRfl
theorem ptD5_1 : allR 30 30
    (pointK 315 9 2 60 DGP5 D5P.F (EF D5E.F) (VF D5R.F) (VF D5L.F)) = true := by quickRfl
theorem ptD5_All : ∀ i < 60,
    (pointK 315 9 2 60 DGP5 D5P.F (EF D5E.F) (VF D5R.F) (VF D5L.F)) i = true :=
  forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact ptD5_0
    · exact ptD5_1

theorem kyD5_0 : allR 0 30
    (keyF D5P.F) = true := by quickRfl
theorem kyD5_1 : allR 30 30
    (keyF D5P.F) = true := by quickRfl
theorem kyD5_All : ∀ i < 60,
    (keyF D5P.F) i = true :=
  forall_of_chunks 30 2 _ fun c hc => by
    interval_cases c
    · exact kyD5_0
    · exact kyD5_1

theorem enumD5 : enumOK 315 (j2FiveDG 5) j2FiveKeyPts (j2FiveDCert 5) = true :=
  enumK_sound' (G := DGP5) hw (by decide) (by decide) hDG5 bD5.1 bD5.2.1 bD5.2.2.1
    (fun i hi => bD5.2.2.2 i hi) (by quickRfl) ptD5_All (keys_of_all kyD5_All)

end CertificateChecks.KernelMisc.J2F

end
