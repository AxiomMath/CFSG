
module

public import Certificates.Kernel.KDense.Y443.Base
public import CFSG.Certificates.Kernel.KDense.Y443.C10107All
public import CFSG.Certificates.Kernel.KDense.Y443.C10108All
public import CFSG.Certificates.Kernel.KDense.Y443.C10110All
public import CFSG.Certificates.Kernel.KDense.Y443.C10112All
public import CFSG.Certificates.Kernel.KDense.Y443.C10113All
public import CFSG.Certificates.Kernel.KDense.Y443.C10114All
public import CFSG.Certificates.Kernel.KDense.Y443.C10120All
public import CFSG.Certificates.Kernel.KDense.Y443.C10121All
public import CFSG.Certificates.Kernel.KDense.Y443.C10122All
public import CFSG.Certificates.Kernel.KDense.Y443.C10124All
public import CFSG.Certificates.Kernel.KDense.Y443.C10125All
public import CFSG.Certificates.Kernel.KDense.Y443.C10126All

public section

namespace CertificateChecks.KernelKDense.Y443

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDense.Y443 CFSG.Monster.AxisCount CFSG.YGroups.Y443

set_option maxRecDepth 100000

theorem hS3 {S : ℕ → St} (h0 : S 0 = CFSG.KD.KDF.I 0) (h1 : S 1 = CFSG.KD.KDF.I 1)
    (h2 : S 2 = CFSG.KD.KDF.I 2) : ∀ x < 3, S x = CFSG.KD.KDF.I x := by
  intro x hx
  interval_cases x <;> assumption

theorem pl10107 : planOK (words pAlign) CFSG.KD.Y443.c10107.CH 29 CFSG.KD.Y443.c10107.IT = true := by quickRfl
theorem pl10108 : planOK (words pAlign) CFSG.KD.Y443.c10108.CH 29 CFSG.KD.Y443.c10108.IT = true := by quickRfl
theorem pl10110 : planOK (words pAlign) CFSG.KD.Y443.c10110.CH 29 CFSG.KD.Y443.c10110.IT = true := by quickRfl
theorem pl10112 : planOK (words pCover) CFSG.KD.Y443.c10112.CH 29 CFSG.KD.Y443.c10112.IT = true := by quickRfl
theorem pl10113 : planOK (words pCover) CFSG.KD.Y443.c10113.CH 29 CFSG.KD.Y443.c10113.IT = true := by quickRfl
theorem pl10114 : planOK (words pCover) CFSG.KD.Y443.c10114.CH 29 CFSG.KD.Y443.c10114.IT = true := by quickRfl
theorem pl10120 : planOK (words pP2) CFSG.KD.Y443.c10120.CH 33 CFSG.KD.Y443.c10120.IT = true := by quickRfl
theorem pl10121 : planOK (words pP2) CFSG.KD.Y443.c10121.CH 33 CFSG.KD.Y443.c10121.IT = true := by quickRfl
theorem pl10122 : planOK (words pP2) CFSG.KD.Y443.c10122.CH 33 CFSG.KD.Y443.c10122.IT = true := by quickRfl
theorem pl10124 : planOK (words pSwap) CFSG.KD.Y443.c10124.CH 10 CFSG.KD.Y443.c10124.IT = true := by quickRfl
theorem pl10125 : planOK (words pSwap) CFSG.KD.Y443.c10125.CH 10 CFSG.KD.Y443.c10125.IT = true := by quickRfl
theorem pl10126 : planOK (words pSwap) CFSG.KD.Y443.c10126.CH 10 CFSG.KD.Y443.c10126.IT = true := by quickRfl

theorem loAlign : pairsLetterOK pAlign = true := by quickRfl
theorem loCover : pairsLetterOK pCover = true := by quickRfl
theorem loP2 : pairsLetterOK pP2 = true := by quickRfl
theorem loSwap : pairsLetterOK pSwap = true := by quickRfl

theorem k10107 : ∀ k < 29, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pAlign) CFSG.KD.Y443.c10107.S
    (CFSG.KD.Y443.c10107.CH k) = true := by kd_all CFSG.KD.Y443.c10107 29
theorem k10108 : ∀ k < 29, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pAlign) CFSG.KD.Y443.c10108.S
    (CFSG.KD.Y443.c10108.CH k) = true := by kd_all CFSG.KD.Y443.c10108 29
theorem k10110 : ∀ k < 29, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pAlign) CFSG.KD.Y443.c10110.S
    (CFSG.KD.Y443.c10110.CH k) = true := by kd_all CFSG.KD.Y443.c10110 29
theorem k10112 : ∀ k < 29, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pCover) CFSG.KD.Y443.c10112.S
    (CFSG.KD.Y443.c10112.CH k) = true := by kd_all CFSG.KD.Y443.c10112 29
theorem k10113 : ∀ k < 29, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pCover) CFSG.KD.Y443.c10113.S
    (CFSG.KD.Y443.c10113.CH k) = true := by kd_all CFSG.KD.Y443.c10113 29
theorem k10114 : ∀ k < 29, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pCover) CFSG.KD.Y443.c10114.S
    (CFSG.KD.Y443.c10114.CH k) = true := by kd_all CFSG.KD.Y443.c10114 29
theorem k10120 : ∀ k < 33, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pP2) CFSG.KD.Y443.c10120.S
    (CFSG.KD.Y443.c10120.CH k) = true := by kd_all CFSG.KD.Y443.c10120 33
theorem k10121 : ∀ k < 33, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pP2) CFSG.KD.Y443.c10121.S
    (CFSG.KD.Y443.c10121.CH k) = true := by kd_all CFSG.KD.Y443.c10121 33
theorem k10122 : ∀ k < 33, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pP2) CFSG.KD.Y443.c10122.S
    (CFSG.KD.Y443.c10122.CH k) = true := by kd_all CFSG.KD.Y443.c10122 33
theorem k10124 : ∀ k < 10, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pSwap) CFSG.KD.Y443.c10124.S
    (CFSG.KD.Y443.c10124.CH k) = true := by kd_all CFSG.KD.Y443.c10124 10
theorem k10125 : ∀ k < 10, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pSwap) CFSG.KD.Y443.c10125.S
    (CFSG.KD.Y443.c10125.CH k) = true := by kd_all CFSG.KD.Y443.c10125 10
theorem k10126 : ∀ k < 10, chunkOK CFSG.KD.KDF.F CFSG.KD.KDT.T (words pSwap) CFSG.KD.Y443.c10126.S
    (CFSG.KD.Y443.c10126.CH k) = true := by kd_all CFSG.KD.Y443.c10126 10

theorem relAlign :
    ∀ t < pAlign.length, wordLin (pAlign.getD t ([], [])).1 = wordLin (pAlign.getD t ([], [])).2 :=
  rel_tri pAlign loAlign pl10107 pl10108 pl10110 k10107 k10108 k10110 (hS3 rfl rfl rfl) (hS3 rfl rfl rfl)
    (hS3 rfl rfl rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem relCover :
    ∀ t < pCover.length, wordLin (pCover.getD t ([], [])).1 = wordLin (pCover.getD t ([], [])).2 :=
  rel_tri pCover loCover pl10112 pl10113 pl10114 k10112 k10113 k10114 (hS3 rfl rfl rfl) (hS3 rfl rfl rfl)
    (hS3 rfl rfl rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem relP2 :
    ∀ t < pP2.length, wordLin (pP2.getD t ([], [])).1 = wordLin (pP2.getD t ([], [])).2 :=
  rel_tri pP2 loP2 pl10120 pl10121 pl10122 k10120 k10121 k10122 (hS3 rfl rfl rfl) (hS3 rfl rfl rfl)
    (hS3 rfl rfl rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem relSwap :
    ∀ t < pSwap.length, wordLin (pSwap.getD t ([], [])).1 = wordLin (pSwap.getD t ([], [])).2 :=
  rel_tri pSwap loSwap pl10124 pl10125 pl10126 k10124 k10125 k10126 (hS3 rfl rfl rfl) (hS3 rfl rfl rfl)
    (hS3 rfl rfl rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem cAlign : wordLin (wcWord ++ omegaWord) = wordLin (omegaWord ++ tWord) :=
  relAlign 0 (by decide)

theorem cCover :
    wordLin (EdgeNoncomm.pairsWord EdgeNoncomm.nP ++ omegaWord) = wordLin (omegaWord ++ coverPHat) ∧
      wordLin (powL 3 coverPHat) = 1 ∧ wordLin (coverQ ++ omegaWord) = wordLin (omegaWord ++ coverQHat) ∧
      wordLin (coverQHat ++ coverPHat ++ coverWy) = wordLin (coverWy ++ tWord) :=
  ⟨relCover 0 (by decide), (relCover 1 (by decide)).trans wordLin_nil, relCover 2 (by decide),
    relCover 3 (by decide)⟩

theorem cP2 :
    wordLin (rhoWord ++ rhoWord) = 1 ∧
      (∀ s ∈ rhoGens, wordLin (Lw s ++ rhoWord) = wordLin (rhoWord ++ Lw (armSwapL s))) ∧
      wordLin (omegaWord ++ mWord) = wordLin (rhoWord ++ omegaWord) ∧
      wordLin (zmWord ++ qWord) = wordLin (qWord ++ tWord) := by
  refine ⟨(relP2 0 (by decide)).trans wordLin_nil, fun s hs => ?_, relP2 8 (by decide), relP2 9 (by decide)⟩
  simp only [rhoGens, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [relP2 1 (by decide), relP2 2 (by decide), relP2 3 (by decide), relP2 4 (by decide),
    relP2 5 (by decide), relP2 6 (by decide), relP2 7 (by decide)]

theorem cSwap :
    wordLin (tWord ++ swap13Word) = wordLin (swap13Word ++ tWord) ∧
      wordLin (mtmWord ++ swap13Word) = wordLin (swap13Word ++ zmWord) :=
  ⟨relSwap 0 (by decide), relSwap 1 (by decide)⟩

end CertificateChecks.KernelKDense.Y443

end
