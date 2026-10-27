module

public import Certificates.Kernel.Misc.RuFive.Q8
public import Certificates.Kernel.Misc.RuFive.Lines
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.SignedWordKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.RuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.SignedWordK
open CFSG.Monster.B.Co2.Native CFSG.RankThree.PartOne CFSG.EvenSporadicStandard.RuStd.S2

theorem gens_eq (k : Nat) (hk : k < 3) : ruFiveC0Gens[k]! = unpack 4060 12 (G k) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound RG.all (k + 64) (show k + 64 < 75 by omega)
  rw [← RG.eq] at h
  have e : ruFiveC0Gens[k]! = ruFiveArr (k + 64) := by
    interval_cases k <;> rfl
  rw [e, ruFiveArr]
  exact h

theorem permG (k : Nat) (hk : k < 3) : permB 4060 12 (G k) = true := by
  interval_cases k
  exacts [permG0, permG1, permG2]

theorem q8 : ruFiveQ8Check = true := by
  have hw := szOK'
  obtain ⟨eI, pI⟩ := signedWordA_unpack hw gens_eq permG q8WordI (by decide)
  obtain ⟨eJ, pJ⟩ := signedWordA_unpack hw gens_eq permG q8WordJ (by decide)
  have hI : swK 4060 12 G q8WordI = I := rfl
  have hJ : swK 4060 12 G q8WordJ = J := rfl
  rw [hI] at eI pI
  rw [hJ] at eJ pJ
  have hid : permB 4060 12 (pidn 4060 12) = true := permB_of_pp (CFSG.KC.BfsPin.PP.id hw)
  unfold ruFiveQ8Check
  rw [eI, eJ, CFSG.KC.BfsPin.validA_unpack pI, CFSG.KC.BfsPin.validA_unpack pJ,
    pow_unpack hw pI 4, pow_unpack hw pI 2, pow_unpack hw pJ 2, CFSG.KC.BfsPin.idA_eq hw,
    eqA_unpack hw (permB_ppow hw pI 4) hid, eqA_unpack hw (permB_ppow hw pI 2) hid,
    eqA_unpack hw (permB_ppow hw pI 2) (permB_ppow hw pJ 2), comp_unpack hw pJ pI,
    inv_unpack hw pJ, comp_unpack hw (permB_pcomp hw pJ pI) (permB_pinvS hw pJ), inv_unpack hw pI,
    eqA_unpack hw (permB_pcomp hw (permB_pcomp hw pJ pI) (permB_pinvS hw pJ))
      (permB_pinvS hw pI), kI4, kI2, kIJ, kRel]
  rfl

end CertificateChecks.KernelMisc.RuFive

end
