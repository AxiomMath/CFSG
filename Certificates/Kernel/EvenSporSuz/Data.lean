module

public import Certificates.Data.Kernel.EvenSporSuz.Defs
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Data.Kernel.EvenSporSuz.Defs
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.CoverCheck
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSuz.SW CFSG.EvenSporadicStandard.TwoSuz.sylowText
#ks_chars CertificateChecks.KernelSuz.JW CFSG.EvenSporadicStandard.TwoSuz.jText
#ks_chars CertificateChecks.KernelSuz.CG CFSG.EvenSporadicStandard.TwoSuz.coverGenText

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.KC.Str CFSG.EvenSporadicStandard.TwoSuz

@[expose] noncomputable def swL (i : ℕ) : List Char := (linesK SW.chars).getD i []

@[expose] noncomputable def jwL (i : ℕ) : List Char := (linesK JW.chars).getD i []

@[expose] noncomputable def cgL (k : ℕ) : List ℕ := matL CG.chars k

@[expose] noncomputable def AR : List ℕ := rowsL (cgL 7)

@[expose] noncomputable def BR : List ℕ := rowsL (cgL 8)

@[expose] noncomputable def abM : List (List ℕ) :=
  [AR, mulR AR AR, mulR (mulR AR AR) AR, BR, mulR BR BR]

@[expose] noncomputable def abI : List (List ℕ) :=
  [mulR (mulR AR AR) AR, mulR AR AR, AR, mulR BR BR, BR]

@[expose] noncomputable def jW : List (List ℕ) :=
  (List.range 4).map (fun i => (natsK (swL (i + 1))).map (2 * ·)) ++ [(natsK (jwL 1)).map (2 * ·)]

@[expose] noncomputable def jM : List (List ℕ) := jW.map (evalR abM abI)

@[expose] noncomputable def jI : List (List ℕ) := jM.map invR

@[expose] noncomputable def uK (j : ℕ) : List ℕ := lettersK (jwL (3 + 2 * j))

@[expose] noncomputable def vK (j : ℕ) : List ℕ := lettersK (jwL (4 + 2 * j))

@[expose] noncomputable def cM : List (List ℕ) :=
  (List.range 2).map fun j => evalR jM jI (uK j ++ vK j ++ invWord (uK j) ++ invWord (vK j))

@[expose] noncomputable def cI : List (List ℕ) :=
  (List.range 2).map fun j => evalR jM jI (vK j ++ uK j ++ invWord (vK j) ++ invWord (uK j))

@[expose] noncomputable def x1R : List ℕ := evalR jM jI (lettersK (swL 5))

@[expose] noncomputable def x2R : List ℕ := evalR jM jI (lettersK (swL 6))

@[expose] noncomputable def jCheckK : Bool :=
  validR abM abI && validR jM jI && validR cM cI &&
    (List.range 5).all (fun i => evalR cM cI (lettersK (jwL (7 + i))) == jM.getD i oneR) &&
    (List.range 5).all fun i =>
      mulR (jM.getD i oneR) x1R == mulR x1R (jM.getD i oneR) &&
        mulR (jM.getD i oneR) x2R == mulR x2R (jM.getD i oneR)

@[expose] noncomputable def inputsOK : Bool :=
  digitsK (swL 0) && decVal (swL 0) == 4 && digitsK (jwL 2) && decVal (jwL 2) == 2 &&
    (List.range 4).all (fun i => ((swL (i + 1)).splitOn ' ').all digitsK) &&
    ((jwL 1).splitOn ' ').all digitsK &&
    [swL 5, swL 6, jwL 3, jwL 4, jwL 5, jwL 6, jwL 7, jwL 8, jwL 9, jwL 10, jwL 11].all
      (fun L => (L.splitOn ' ').all tokK) &&
    (nonEmptyLines CG.chars).length / 12 == 9 &&
    ((cgL 7).length == 144 && (cgL 7).all (· < 3)) && ((cgL 8).length == 144 && (cgL 8).all (· < 3))

set_option maxHeartbeats 0 in
theorem inputsOK_true : inputsOK = true := by decide +kernel

meta def swLM (i : ℕ) : List Char := (linesK sylowText.toList).getD i []
meta def jwLM (i : ℕ) : List Char := (linesK jText.toList).getD i []
meta def ARM : List ℕ := rowsL (matL coverGenText.toList 7)
meta def BRM : List ℕ := rowsL (matL coverGenText.toList 8)
meta def abMM : List (List ℕ) := [ARM, mulR ARM ARM, mulR (mulR ARM ARM) ARM, BRM, mulR BRM BRM]
meta def abIM : List (List ℕ) := [mulR (mulR ARM ARM) ARM, mulR ARM ARM, ARM, mulR BRM BRM, BRM]
meta def jRM (i : ℕ) : List ℕ :=
  evalR abMM abIM ((natsK (if i < 4 then swLM (i + 1) else jwLM 1)).map (2 * ·))
meta def jRM0 : List ℕ := jRM 0
meta def jRM1 : List ℕ := jRM 1
meta def jRM2 : List ℕ := jRM 2
meta def jRM3 : List ℕ := jRM 3
meta def jRM4 : List ℕ := jRM 4
meta def jWM (i : ℕ) : List ℕ := (natsK (if i < 4 then swLM (i + 1) else jwLM 1)).map (2 * ·)
meta def jPM (i k : ℕ) : List ℕ := evalR abMM abIM ((jWM i).take k)
meta def jWM0 : List ℕ := jWM 0
meta def jPM0a : List ℕ := jPM 0 600
meta def jPM0b : List ℕ := jPM 0 1200
meta def jPM0c : List ℕ := jPM 0 1800
meta def jWM1 : List ℕ := jWM 1
meta def jPM1a : List ℕ := jPM 1 600
meta def jPM1b : List ℕ := jPM 1 1200
meta def jPM1c : List ℕ := jPM 1 1800
meta def jWM2 : List ℕ := jWM 2
meta def jPM2a : List ℕ := jPM 2 600
meta def jPM2b : List ℕ := jPM 2 1200
meta def jPM2c : List ℕ := jPM 2 1800
meta def jWM3 : List ℕ := jWM 3
meta def jPM3a : List ℕ := jPM 3 600
meta def jPM3b : List ℕ := jPM 3 1200
meta def jPM3c : List ℕ := jPM 3 1800
meta def jWM4 : List ℕ := jWM 4
meta def jPM4a : List ℕ := jPM 4 600
meta def jPM4b : List ℕ := jPM 4 1200
meta def jPM4c : List ℕ := jPM 4 1800

end CertificateChecks.KernelSuz

#knatlist CertificateChecks.KernelSuz.JR0 CertificateChecks.KernelSuz.jRM0
#knatlist CertificateChecks.KernelSuz.JR1 CertificateChecks.KernelSuz.jRM1
#knatlist CertificateChecks.KernelSuz.JR2 CertificateChecks.KernelSuz.jRM2
#knatlist CertificateChecks.KernelSuz.JR3 CertificateChecks.KernelSuz.jRM3
#knatlist CertificateChecks.KernelSuz.JR4 CertificateChecks.KernelSuz.jRM4
#knatlist CertificateChecks.KernelSuz.JW0 CertificateChecks.KernelSuz.jWM0
#knatlist CertificateChecks.KernelSuz.JP0a CertificateChecks.KernelSuz.jPM0a
#knatlist CertificateChecks.KernelSuz.JP0b CertificateChecks.KernelSuz.jPM0b
#knatlist CertificateChecks.KernelSuz.JP0c CertificateChecks.KernelSuz.jPM0c
#knatlist CertificateChecks.KernelSuz.JW1 CertificateChecks.KernelSuz.jWM1
#knatlist CertificateChecks.KernelSuz.JP1a CertificateChecks.KernelSuz.jPM1a
#knatlist CertificateChecks.KernelSuz.JP1b CertificateChecks.KernelSuz.jPM1b
#knatlist CertificateChecks.KernelSuz.JP1c CertificateChecks.KernelSuz.jPM1c
#knatlist CertificateChecks.KernelSuz.JW2 CertificateChecks.KernelSuz.jWM2
#knatlist CertificateChecks.KernelSuz.JP2a CertificateChecks.KernelSuz.jPM2a
#knatlist CertificateChecks.KernelSuz.JP2b CertificateChecks.KernelSuz.jPM2b
#knatlist CertificateChecks.KernelSuz.JP2c CertificateChecks.KernelSuz.jPM2c
#knatlist CertificateChecks.KernelSuz.JW3 CertificateChecks.KernelSuz.jWM3
#knatlist CertificateChecks.KernelSuz.JP3a CertificateChecks.KernelSuz.jPM3a
#knatlist CertificateChecks.KernelSuz.JP3b CertificateChecks.KernelSuz.jPM3b
#knatlist CertificateChecks.KernelSuz.JP3c CertificateChecks.KernelSuz.jPM3c
#knatlist CertificateChecks.KernelSuz.JW4 CertificateChecks.KernelSuz.jWM4
#knatlist CertificateChecks.KernelSuz.JP4a CertificateChecks.KernelSuz.jPM4a
#knatlist CertificateChecks.KernelSuz.JP4b CertificateChecks.KernelSuz.jPM4b
#knatlist CertificateChecks.KernelSuz.JP4c CertificateChecks.KernelSuz.jPM4c

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.KC.Str CFSG.EvenSporadicStandard.TwoSuz

@[expose] def stepR (M I : List (List ℕ)) (acc : List ℕ) (c : ℕ) : List ℕ := mulR acc (letterR M I c)

theorem evalR_eq_foldl (M I : List (List ℕ)) (w : List ℕ) : evalR M I w = w.foldl (stepR M I) oneR :=
  rfl

theorem foldl_split {M I : List (List ℕ)} {w X Y Z : List ℕ} (n : ℕ)
    (h1 : ((w.take n).foldl (stepR M I) X == Y) = true)
    (h2 : ((w.drop n).foldl (stepR M I) Y == Z) = true) :
    (w.foldl (stepR M I) X == Z) = true := by
  rw [← List.take_append_drop n w, List.foldl_append, eq_of_beq h1]
  exact h2

theorem jW0 : ((natsK (swL 1)).map (2 * ·) == JW0) = true := by quickRfl
theorem jR0a : ((JW0.take 600).foldl (stepR abM abI) oneR == JP0a) = true := by quickRfl
theorem jR0b : (((JW0.drop 600).take 600).foldl (stepR abM abI) JP0a == JP0b) = true := by
  quickRfl
theorem jR0c : ((((JW0.drop 600).drop 600).take 600).foldl (stepR abM abI) JP0b == JP0c) =
    true := by
  quickRfl
theorem jR0d : ((((JW0.drop 600).drop 600).drop 600).foldl (stepR abM abI) JP0c == JR0) =
    true := by
  quickRfl
theorem jR0 : (evalR abM abI ((natsK (swL 1)).map (2 * ·)) == JR0) = true := by
  rw [eq_of_beq jW0, evalR_eq_foldl]
  exact foldl_split 600 jR0a (foldl_split 600 jR0b (foldl_split 600 jR0c jR0d))

theorem jW1 : ((natsK (swL 2)).map (2 * ·) == JW1) = true := by quickRfl
theorem jR1a : ((JW1.take 600).foldl (stepR abM abI) oneR == JP1a) = true := by quickRfl
theorem jR1b : (((JW1.drop 600).take 600).foldl (stepR abM abI) JP1a == JP1b) = true := by
  quickRfl
theorem jR1c : ((((JW1.drop 600).drop 600).take 600).foldl (stepR abM abI) JP1b == JP1c) =
    true := by
  quickRfl
theorem jR1d : ((((JW1.drop 600).drop 600).drop 600).foldl (stepR abM abI) JP1c == JR1) =
    true := by
  quickRfl
theorem jR1 : (evalR abM abI ((natsK (swL 2)).map (2 * ·)) == JR1) = true := by
  rw [eq_of_beq jW1, evalR_eq_foldl]
  exact foldl_split 600 jR1a (foldl_split 600 jR1b (foldl_split 600 jR1c jR1d))

theorem jW2 : ((natsK (swL 3)).map (2 * ·) == JW2) = true := by quickRfl
theorem jR2a : ((JW2.take 600).foldl (stepR abM abI) oneR == JP2a) = true := by quickRfl
theorem jR2b : (((JW2.drop 600).take 600).foldl (stepR abM abI) JP2a == JP2b) = true := by
  quickRfl
theorem jR2c : ((((JW2.drop 600).drop 600).take 600).foldl (stepR abM abI) JP2b == JP2c) =
    true := by
  quickRfl
theorem jR2d : ((((JW2.drop 600).drop 600).drop 600).foldl (stepR abM abI) JP2c == JR2) =
    true := by
  quickRfl
theorem jR2 : (evalR abM abI ((natsK (swL 3)).map (2 * ·)) == JR2) = true := by
  rw [eq_of_beq jW2, evalR_eq_foldl]
  exact foldl_split 600 jR2a (foldl_split 600 jR2b (foldl_split 600 jR2c jR2d))

theorem jW3 : ((natsK (swL 4)).map (2 * ·) == JW3) = true := by quickRfl
theorem jR3a : ((JW3.take 600).foldl (stepR abM abI) oneR == JP3a) = true := by quickRfl
theorem jR3b : (((JW3.drop 600).take 600).foldl (stepR abM abI) JP3a == JP3b) = true := by
  quickRfl
theorem jR3c : ((((JW3.drop 600).drop 600).take 600).foldl (stepR abM abI) JP3b == JP3c) =
    true := by
  quickRfl
theorem jR3d : ((((JW3.drop 600).drop 600).drop 600).foldl (stepR abM abI) JP3c == JR3) =
    true := by
  quickRfl
theorem jR3 : (evalR abM abI ((natsK (swL 4)).map (2 * ·)) == JR3) = true := by
  rw [eq_of_beq jW3, evalR_eq_foldl]
  exact foldl_split 600 jR3a (foldl_split 600 jR3b (foldl_split 600 jR3c jR3d))

theorem jW4 : ((natsK (jwL 1)).map (2 * ·) == JW4) = true := by quickRfl
theorem jR4a : ((JW4.take 600).foldl (stepR abM abI) oneR == JP4a) = true := by quickRfl
theorem jR4b : (((JW4.drop 600).take 600).foldl (stepR abM abI) JP4a == JP4b) = true := by
  quickRfl
theorem jR4c : ((((JW4.drop 600).drop 600).take 600).foldl (stepR abM abI) JP4b == JP4c) =
    true := by
  quickRfl
theorem jR4d : ((((JW4.drop 600).drop 600).drop 600).foldl (stepR abM abI) JP4c == JR4) =
    true := by
  quickRfl
theorem jR4 : (evalR abM abI ((natsK (jwL 1)).map (2 * ·)) == JR4) = true := by
  rw [eq_of_beq jW4, evalR_eq_foldl]
  exact foldl_split 600 jR4a (foldl_split 600 jR4b (foldl_split 600 jR4c jR4d))

theorem jM_eq : jM = [JR0, JR1, JR2, JR3, JR4] := by
  have hW : jW = [(natsK (swL 1)).map (2 * ·), (natsK (swL 2)).map (2 * ·),
      (natsK (swL 3)).map (2 * ·), (natsK (swL 4)).map (2 * ·), (natsK (jwL 1)).map (2 * ·)] := by
    rfl
  rw [jM, hW]
  simp only [List.map_cons, List.map_nil]
  rw [eq_of_beq jR0, eq_of_beq jR1, eq_of_beq jR2, eq_of_beq jR3, eq_of_beq jR4]

set_option maxHeartbeats 0 in
theorem jCheckK_true : jCheckK = true := by
  unfold jCheckK cM cI x1R x2R jI
  rw [jM_eq]
  quickRfl

end CertificateChecks.KernelSuz
