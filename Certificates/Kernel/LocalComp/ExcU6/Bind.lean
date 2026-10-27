module

public import Certificates.Kernel.LocalComp.ExcU6.Data2
public import Certificates.Kernel.LocalComp.ExcU6.Data3
public import Certificates.Kernel.LocalComp.ExcU6.DataS
public import Certificates.Kernel.LocalComp.ExcU6.Derivs
public import Certificates.Kernel.LocalComp.ExcGlue
public import Certificates.Kernel.UnitarySix.ChainFacts
public import Certificates.Kernel.UnitarySix.Letters
public import CFSG.Certificates.Kernel.LocalCompExcU6Sound
public import CFSG.Certificates.Kernel.U6Sound3010S
public import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelLC.ExcU6

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.M12Cover
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.M11
open CFSG.KS.SporSch.CodesImg CFSG.KC.Child3 CFSG.KC.LocalComp.ExcDeriv
open CFSG.ComponentClassification.RankTwoClassical.ExcU6 CFSG.EvenSmallLie.UnitarySix
open CertificateChecks.KernelLC.ExcGlue CertificateChecks.KernelU6

@[expose] noncomputable def ALI (j : Nat) : Nat := pinvS 693 10 (mask 10) (lget ALL j)

theorem sz : szOK 693 10 = true := by quickRfl

theorem kId : idK 693 10 (mask 10) = true := by quickRfl

theorem one693 : imageList (1 : Equiv.Perm (Fin 693)) = (unpack 693 10 (pidn 693 10)).toList :=
  one_img kId

theorem cOne : canonK 693 10 (mask 10) (693 * 10) One693 = true := by quickRfl

theorem imgRep {g : Equiv.Perm (Fin 693)} {P : Nat}
    (h : CFSG.Monster.B.Co2.Rep 693 (unpack 693 10 P) g) :
    imageList g = (unpack 693 10 P).toList :=
  CertificateChecks.KernelLQT.He4148.imageList_of_rep
    (CertificateChecks.KernelLQT.He4148.unpack_size' _ _ _) h

theorem letterWords_len : letterWords.length = 46 := by
  unfold letterWords
  rw [List.length_map, List.length_range]

theorem letterWords_get (k : Nat) (hk : k < letterWords.length) :
    letterWords[k] = [Int.ofNat k + 1] := by
  simp [letterWords]

theorem letters_map : u62Letters = letterWords.map u62W := by
  apply List.ext_getElem
  · rw [letters_eq.1, List.length_map, letterWords_len]
  · intro k h1 h2
    have hk : k < letterWords.length := by simpa using h2
    rw [List.getElem_map, letterWords_get k hk, u62W, tab_eq, evalCodes, evalCodes, mul_one]
    have hp : (0 : ℤ) < Int.ofNat k + 1 := by simp only [Int.ofNat_eq_coe]; omega
    rw [ite_eq_left hp]
    have ht : (Int.ofNat k + 1).toNat - 1 = k := by simp only [Int.ofNat_eq_coe]; omega
    rw [ht, List.getD_eq_getElem _ _ h1]

theorem alphabet_eq : alphabet = alWords.map u62W := by
  rw [alphabet, alWords, letters_map]
  simp only [List.map_append, List.map_cons, List.map_nil]
  rfl

theorem alWN_eq : alWords = alWN.map (List.map CFSG.KC.U6.decZ) := by decide +kernel

theorem alWN_lt : ∀ w ∈ alWN, ∀ c ∈ w, c < 92 := by decide +kernel

theorem kAL : CFSG.KC.U6.bindsK U.LT alWN (lget ALL) = true := by quickRfl

theorem alphabet_len : alphabet.length = 64 := by
  rw [alphabet_eq, List.length_map]
  decide +kernel

theorem imgA : ∀ j < alphabet.length, imageList (alphabet.getD j 1) =
    (unpack 693 10 (lget ALL j)).toList := by
  have hb := CFSG.KC.U6.soundBinds letters_eq alWN_eq alWN_lt kAL
  rw [alphabet_eq]
  intro j hj
  exact imgRep (hb j (by simpa using hj))

theorem kAI : allN 64 (fun j => permOK 693 10 (mask 10) (693 * 10) (lget ALL j) (ALI j)) = true := by
  quickRfl

theorem pA : ∀ j < alphabet.length, permOK 693 10 (mask 10) (693 * 10) (lget ALL j) (ALI j) = true :=
  fun j hj => allN_spec kAI j (lt_of_lt_of_eq hj alphabet_len)

theorem sGens_eq : sGens = (aWords ++ tWords).map u62W := by
  rw [sGens, aGens, tGens, List.map_append]

theorem sGens_len : sGens.length = 13 := by rw [sGens_eq, List.length_map]; rfl

theorem imgS : ∀ j < sGens.length, imageList (sGens.getD j 1) = (unpack 693 10 (SQ.S j)).toList := by
  have hb := CFSG.KC.U6.soundBinds (ws := aWords ++ tWords) letters_eq
    (by rw [aWN_eq, tWN_eq, List.map_append]) (by decide +kernel) SQ.kBinds
  rw [sGens_eq]
  intro j hj
  exact imgRep (hb j (by simpa using hj))

theorem pS : ∀ j < sGens.length, permOK 693 10 (mask 10) (693 * 10) (SQ.S j) (SQ.SI j) = true :=
  fun j hj => allN_spec SQ.perm j (by rw [sGens_len] at hj; omega)

theorem aGens_eq : aGens = aWords.map u62W := rfl

theorem aGens_len : aGens.length = 9 := by rw [aGens_eq, List.length_map]; rfl

theorem imgAq : ∀ j < aGens.length, imageList (aGens.getD j 1) = (unpack 693 10 (AQ.S j)).toList := by
  have hb := CFSG.KC.U6.soundBinds (ws := aWords) letters_eq aWN_eq (by decide +kernel) AQ.kBinds
  rw [aGens_eq]
  intro j hj
  exact imgRep (hb j (by simpa using hj))

theorem pAq : ∀ j < aGens.length, permOK 693 10 (mask 10) (693 * 10) (AQ.S j) (AQ.SI j) = true :=
  fun j hj => allN_spec AQ.perm j (by rw [aGens_len] at hj; omega)

theorem kX2 : Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) SQ.S SQ.SI [2, 3]) X2 = true := by
  quickRfl
theorem kX3 : Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) SQ.S SQ.SI [3, 6, 9]) X3 = true := by
  quickRfl
theorem kJ1 : Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) AQ.S AQ.SI [1]) J1 = true := by
  quickRfl

theorem imgX2 : imageList x2 = (unpack 693 10 X2).toList := by
  have h1 : lettersK sGens.length [2, 3] = true := by rw [sGens_len]; quickRfl
  rw [x2, evalCodes_img sz imgS pS one693 h1, Nat.eq_of_beq_eq_true kX2]

theorem imgX3 : imageList x3 = (unpack 693 10 X3).toList := by
  have h1 : lettersK sGens.length [3, 6, 9] = true := by rw [sGens_len]; quickRfl
  rw [x3, evalCodes_img sz imgS pS one693 h1, Nat.eq_of_beq_eq_true kX3]

theorem imgJ1 : imageList j1 = (unpack 693 10 J1).toList := by
  have h1 : lettersK aGens.length [1] = true := by rw [aGens_len]; quickRfl
  rw [j1, evalCodes_img sz imgAq pAq one693 h1, Nat.eq_of_beq_eq_true kJ1]

theorem s2Gens_eq : s2Gens = s2Words.map (evalCodes sGens) := by simp only [s2Gens, tab_eq]
theorem s3Gens_eq : s3Gens = s3Words.map (evalCodes sGens) := by simp only [s3Gens, tab_eq]

theorem s2Gens_len : s2Gens.length = 8 := by rw [s2Gens_eq, List.length_map]; rfl
theorem s3Gens_len : s3Gens.length = 11 := by rw [s3Gens_eq, List.length_map]; rfl

theorem kS2 : allN s2Words.length (fun j => bAnd(lettersK 13 (s2Words.getD j []),
    Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) SQ.S SQ.SI (s2Words.getD j [])) (Q2.S j))) =
    true := by quickRfl
theorem kS3 : allN s3Words.length (fun j => bAnd(lettersK 13 (s3Words.getD j []),
    Nat.beq (wordK 693 10 (mask 10) (pidn 693 10) SQ.S SQ.SI (s3Words.getD j [])) (Q3.S j))) =
    true := by quickRfl

theorem img2 : ∀ j < s2Gens.length, imageList (s2Gens.getD j 1) =
    (unpack 693 10 (Q2.S j)).toList := by
  rw [s2Gens_eq]
  intro j hj
  exact words_img sGens_len sz imgS pS one693 kS2 j (by simpa using hj)

theorem img3 : ∀ j < s3Gens.length, imageList (s3Gens.getD j 1) =
    (unpack 693 10 (Q3.S j)).toList := by
  rw [s3Gens_eq]
  intro j hj
  exact words_img sGens_len sz imgS pS one693 kS3 j (by simpa using hj)

theorem kP2 : allN 8 (fun j => permOK 693 10 (mask 10) (693 * 10) (Q2.S j) (Q2.SI j)) = true := by
  quickRfl
theorem kP3 : allN 11 (fun j => permOK 693 10 (mask 10) (693 * 10) (Q3.S j) (Q3.SI j)) = true := by
  quickRfl

theorem p2 : ∀ j < s2Gens.length, permOK 693 10 (mask 10) (693 * 10) (Q2.S j) (Q2.SI j) = true :=
  fun j hj => allN_spec kP2 j (lt_of_lt_of_eq hj s2Gens_len)
theorem p3 : ∀ j < s3Gens.length, permOK 693 10 (mask 10) (693 * 10) (Q3.S j) (Q3.SI j) = true :=
  fun j hj => allN_spec kP3 j (lt_of_lt_of_eq hj s3Gens_len)

theorem chainA : ChainK 693 10 aGens aDer (#v[1, 3, 45] : Vector (Fin 693) 3)
    AQ.S AQ.SI AQ.LR AQ.TR AQ.TRI 12 AQ.BP 11 64 :=
  ⟨by norm_num, by norm_num, by norm_num, imgAq, by decide, AQ.head, AQ.hl, by norm_num, AQ.hs⟩

theorem chain2 : ChainK 693 10 s2Gens s2QWords (#v[1, 45, 3] : Vector (Fin 693) 3)
    Q2.S Q2.SI Q2.LR Q2.TR Q2.TRI 12 Q2.BP 11 64 :=
  ⟨by norm_num, by norm_num, by norm_num, img2, by decide, Q2.head, Q2.hl, by norm_num, Q2.hs⟩

theorem chain3 : ChainK 693 10 s3Gens s3QWords (#v[1, 3, 45] : Vector (Fin 693) 3)
    Q3.S Q3.SI Q3.LR Q3.TR Q3.TRI 14 Q3.BP 11 64 :=
  ⟨by norm_num, by norm_num, by norm_num, img3, by decide, Q3.head, Q3.hl, by norm_num, Q3.hs⟩

theorem kN2 : Nat.beq (ordK Q2.LR 3) 16384 = true := by quickRfl
theorem kN3 : Nat.beq (ordK Q3.LR 3) 4096 = true := by quickRfl

theorem kM2 : allN 8 (fun j => Nat.beq (pcomp 693 10 (mask 10) (Q2.S j) X2)
    (pcomp 693 10 (mask 10) X2 (Q2.S j))) = true := by quickRfl
theorem kM3 : allN 11 (fun j => Nat.beq (pcomp 693 10 (mask 10) (Q3.S j) X3)
    (pcomp 693 10 (mask 10) X3 (Q3.S j))) = true := by quickRfl

theorem chain_check : censusChainCheck = true := by
  obtain ⟨hc2, ho2⟩ : s2Q.check = true ∧ s2Q.orderCertificate = ordK Q2.LR 3 :=
    chainK_check (by decide) (by decide) chain2
  obtain ⟨hc3, ho3⟩ : s3Q.check = true ∧ s3Q.orderCertificate = ordK Q3.LR 3 :=
    chainK_check (by decide) (by decide) chain3
  unfold censusChainCheck
  rw [hc2, ho2, Nat.eq_of_beq_eq_true kN2, hc3, ho3, Nat.eq_of_beq_eq_true kN3,
    comm_all s2Gens_len sz img2 imgX2 kM2, comm_all s3Gens_len sz img3 imgX3 kM3]
  rfl

theorem cX2 : canonK 693 10 (mask 10) (693 * 10) X2 = true := by quickRfl
theorem cX3 : canonK 693 10 (mask 10) (693 * 10) X3 = true := by quickRfl

theorem kSX2 : siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) AQ.LR AQ.TRI AQ.BP 3 0 X2 = true := by
  quickRfl
theorem kSX3 : siftK 693 10 (mask 10) (693 * 10) (pidn 693 10) AQ.LR AQ.TRI AQ.BP 3 0 X3 = true := by
  quickRfl

theorem kF2 : Nat.beq (fixCntK 10 (mask 10) X2 693) 53 = true := by quickRfl
theorem kF3 : Nat.beq (fixCntK 10 (mask 10) X3 693) 21 = true := by quickRfl
theorem kFJ : Nat.beq (fixCntK 10 (mask 10) J1 693) 181 = true := by quickRfl

theorem point_check : censusPointCheck = true := by
  have h2 : aQ.sift x2 0 = true := chainK_sift (by decide) (by decide) chainA imgX2 cX2 kSX2
  have h3 : aQ.sift x3 0 = true := chainK_sift (by decide) (by decide) chainA imgX3 cX3 kSX3
  unfold censusPointCheck
  rw [h2, h3, fixCount_img imgX2, fixCount_img imgX3, fixCount_img imgJ1,
    Nat.eq_of_beq_eq_true kF2, Nat.eq_of_beq_eq_true kF3, Nat.eq_of_beq_eq_true kFJ]
  rfl

end CertificateChecks.KernelLC.ExcU6

end
