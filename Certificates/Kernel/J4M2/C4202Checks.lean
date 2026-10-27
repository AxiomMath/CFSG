module

public import Certificates.Data.Kernel.J4M2Hex
public import CFSG.Certificates.Kernel.Common.Each

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.Enum CFSG.KC.LQT.L CFSG.KS.PK CFSG.KC.J4M2K CFSG.Quasithin.J4M2
  CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat

@[expose] noncomputable def ch4202sig (n : Nat) : Bool :=
  (List.range 77).all fun i => ((sigPerm n) (Fin.ofNat 77 i)).val == (sigData.getD n []).getD i 0

#kc_each ch4202sig 0 32

theorem ch4202hexLab :
    (hexLab.length == 77 && hexLab.all (fun h => h.length == 6 && h.all (· < 22))) = true := by
  decide +kernel

theorem ch4202dist : distChk = true := by decide +kernel

@[expose] noncomputable def ch4202gen (k : Nat) : Bool := hexGenK k

#kc_each ch4202gen 0 25

theorem ch4202words : wordsChk = true := by decide +kernel

theorem ch4202t : tChk = true := by decide +kernel

@[expose] noncomputable def ch4202class (j : Nat) : Bool := classK j

#kc_each ch4202class 0 6

theorem ch4202p0 : p0Chk = true := by decide +kernel

theorem ch4202neg_sig :
    ((List.range 77).all fun i =>
      ((sigPerm 12) (Fin.ofNat 77 i)).val == (sigData.getD 13 []).getD i 0) = false := by
  decide +kernel

theorem ch4202neg_dist :
    distK (pmk 77 22 fun i => maskL (hexLab.getD (bif Nat.beq i 5 then 0 else i) [])) = false := by
  decide +kernel

theorem ch4202neg_gen :
    (strictB hexP fun H => strictB (gimg (Equiv.swap 0 1)) fun G => permK H (fd 5 G)) = false := by
  decide +kernel

theorem ch4202neg_words :
    (strictB hexP fun H => strictB (phiC H (gimg (mGens.getD 0 1))) fun A =>
      strictB (phiC H (gimg (mGens.getD 1 1))) fun B =>
        wordsCore A B [sigC 13, sigC 12, sigC 14, sigC 15, sigC 16]) = false := by
  decide +kernel

theorem ch4202neg_t :
    (strictB (sigC 28) fun a => strictB (sigC 29) fun b => strictB (sigC 30) fun c =>
      tCore (bfsK7 77 [a, b, c] 64) [a, b, c] ((List.range 15).map fun j => sigC (17 + j))
        []) = false := by
  decide +kernel

theorem ch4202neg_class :
    (strictB hexP fun H =>
      bIf(allA (members.getD 4 []) fun g => strictB (gimg g) fun G => fixK (phiK H (fd 5 G)),
        true,
        allA (members.getD 4 []) fun g => strictB (gimg g) fun G => presK (phiK H (fd 5 G))))
      = false := by
  decide +kernel

theorem ch4202neg_p0 :
    (allR 5 fun j => bAnd(fixK fun i => (sigData.getD (12 + j) []).getD i 0,
      presK fun i => (sigData.getD (12 + j) []).getD i 0)) = false := by
  decide +kernel

end CertificateChecks.KernelJ4M2

end
