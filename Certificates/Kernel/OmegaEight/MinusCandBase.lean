module

public import Certificates.Kernel.OmegaEight.MinusW
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelO8

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage2.MinusW

@[expose] noncomputable def candPM (m : ℕ) : Bool :=
  !(enMemK EnC2M.D EnC2M.m (mul12K m m) && fpowAuxK 64 m 256 ID12 == ID12 &&
      Minus.samples.all fun c =>
        enMemK EnC2M.D EnC2M.m (mul12K (mul12K m c) (fpowAuxK 64 m 255 ID12))) ||
    Minus.reps.any fun r => enMemK EnCM.D EnCM.m (mul12K r.2 m)

@[expose] noncomputable def tuplesM : List (List ℕ) :=
  (((List.range EnP3M.m).map (enKey EnP3M.D)).filter (· != ID12)).flatMap fun z₁ =>
    (((List.range EnP3M.m).map (enKey EnP3M.D)).filter fun z₂ =>
      z₂ != ID12 && z₂ != z₁ && z₂ != mul12K z₁ z₁).map fun z₂ => [z₁, z₂]

@[expose] noncomputable def candSysM (a b : ℕ) : Bool :=
  linCheckWith (candCons (tuplesM.getD b []) Minus.ys (Minus.cases.getD a []))
      (MwLin a b).1 (MwLin a b).2.1 (MwLin a b).2.2 &&
    spanAll (MwLin a b).2.1 (MwLin a b).2.2.length candPM

theorem tuples_wM : tuples wM = tuplesM := by
  simp only [tuples, wM, decE_toList, mulK_eq, idK_eq, tuplesM]

theorem candP_eqM : (fun m => !(candFilter wM.c2E Minus.samples m) || repOK wM.cE Minus.reps m) =
    candPM := by
  have hsC : sortedK (decE EnCM.D EnCM.m).keys = true := (Enum.of_enumOK cE_okM).2.1
  have hs2 : sortedK (decE EnC2M.D EnC2M.m).keys = true := (Enum.of_enumOK c2E_okM).2.1
  funext m
  simp only [candFilter, repOK, wM, fpowK_eq, mulK_eq, idK_eq,
    memK_decE_eq hsC (by decide +kernel), memK_decE_eq hs2 (by decide +kernel), candPM]

end CertificateChecks.KernelO8
