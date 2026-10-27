module

public import Certificates.Data.Kernel.EvenSporSuz.Defs
public import Certificates.Kernel.Sporadic.RawGen
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

set_option maxHeartbeats 0 in
theorem jCheckK_true : jCheckK = true := by decide +kernel

end CertificateChecks.KernelSuz
