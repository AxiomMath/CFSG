module

public import Certificates.Kernel.HeLoc.DihKChecks
public import Certificates.Kernel.HeLoc.SevenBase
public import CFSG.Certificates.Kernel.HeDihKSound

public section

namespace CertificateChecks.KernelHeLoc.Seven

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HeDih CFSG.RankThree.PartOne
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.PartTwo.KFacts.K426
open CFSG.RankThree.Native CFSG.Certificates.Native

theorem dihSz : szOK 8330 14 = true := by decide

theorem c1K_eq (k : Nat) (hk : k < 3) : heSevenC1Gens[k]! = unpack 8330 14 (c1K k) := by
  rw [heSevenC1Gens]
  interval_cases k
  · exact (lit3_0 _ _ _).trans (arr_eq 65 (by norm_num))
  · exact (lit3_1 _ _ _).trans (arr_eq 66 (by norm_num))
  · exact (lit3_2 _ _ _).trans (arr_eq 67 (by norm_num))

theorem c1K_pp (k : Nat) (hk : k < 3) : PP 8330 14 (c1K k) :=
  CFSG.KC.Misc.ArrEnum.pp_of_permOK dihSz (perm_k (65 + k) (by omega))

theorem heSevenDihedralOK_of : heSevenDihedralOK () = true := by
  obtain ⟨hρ, hr⟩ := evalWA_unpack dihSz c1K_eq c1K_pp heSevenRhoWord
  obtain ⟨hσ, hs⟩ := evalWA_unpack dihSz c1K_eq c1K_pp heSevenSigmaWord
  have hd := dih10128
  rw [dihWK_eq] at hd
  generalize evalWK 8330 14 c1K heSevenRhoWord = r at hρ hr hd
  generalize evalWK 8330 14 c1K heSevenSigmaWord = s at hσ hs hd
  have hv : allLt 3 (fun k => validA 8330 heSevenC1Gens[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    rw [c1K_eq k hk]
    exact validA_unpack (CFSG.KC.Misc.ArrEnum.permB_of_pp (c1K_pp k hk))
  unfold dihK at hd
  simp only [Bool.and_eq_true] at hd
  obtain ⟨h1, ⟨⟨h20, h21⟩, h22⟩, h23⟩ := hd
  have hall : allLt 4 (fun k => !eqA 8330 (heSevenSigmaArr ())
      (CFSG.Monster.B.Mathieu.powArr 8330 (heSevenRhoArr ()) k)) = true := by
    rw [allLt_iff]
    intro k hk
    rw [heSevenSigmaArr, heSevenRhoArr, hσ, hρ, eqA_pow dihSz hr hs]
    interval_cases k
    · exact h20
    · exact h21
    · exact h22
    · exact h23
  unfold heSevenDihedralOK
  dsimp only
  rw [hv, hall, heSevenSigmaArr, heSevenRhoArr, hσ, hρ, pow_unpack dihSz hr, pow_unpack dihSz hr,
    pow_unpack dihSz hr, idA_eq dihSz, compA_PP hs hs, compA_PP hr hs, compA_PP hs (hr.mul hs),
    eqA_PP (pp_powK dihSz hr 4) (PP.id dihSz), eqA_PP (pp_powK dihSz hr 2) (PP.id dihSz),
    eqA_PP (hs.mul hs) (PP.id dihSz), eqA_PP (hs.mul (hr.mul hs)) (pp_powK dihSz hr 3)]
  simpa only [Bool.true_and, Bool.and_true, Bool.and_eq_true] using h1

end CertificateChecks.KernelHeLoc.Seven

end
