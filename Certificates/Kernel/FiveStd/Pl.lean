module

public import Certificates.Kernel.FiveStd.Data
public import Certificates.Kernel.FiveStd.ClsData
public import Certificates.Kernel.FiveStd.PlData
public import Certificates.Kernel.FiveStd.Cover
public import Certificates.Data.Kernel.FiveStdKOrb
public import Certificates.Data.Kernel.FiveStdKPl
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.FiveStd

open CFSG.KC.FiveStdK

set_option Elab.async false

@[expose] noncomputable def plF (k : Nat) : Bool :=
  clsOK G GI 2 (PU.getD k 0) (PR.getD k 0) (PM.getD k 0) (PB.getD k 0) (PC.getD k 0) oneK

#kc_each CertificateChecks.FiveStd.ch5147p p (fun k => plF k) 0 3

@[expose] def PL0 : List Nat :=
  [18780, 409405, 18815, 409440, 18835, 409460, 18870, 409495, 21915, 412540, 21945, 412570, 21955,
    412580, 21985, 412610, 25035, 415660, 25055, 415680, 25095, 415720, 25115, 415740, 28170, 418795,
    28185, 418810, 28215, 418840, 28230, 418855, 78876, 469501, 79003, 469628, 79127, 469752, 79254,
    469879, 79503, 470128, 79629, 470254, 79751, 470376, 79877, 470502, 80127, 470752, 80251, 470876,
    80379, 471004, 80503, 471128, 80754, 471379, 80877, 471502, 81003, 471628, 81126, 471751]

@[expose] def PL2 : List Nat :=
  [18815, 18835, 19002, 19128, 412570, 412580, 412627, 413003, 415680, 415720, 415753, 416127, 28185,
    28215, 28378, 28502, 78795, 78855, 78876, 79254, 470055, 470095, 470128, 470502, 470695, 470705,
    470752, 471128, 80655, 80745, 80754, 81126, 492789, 492869, 492911, 492991, 495291, 495361, 495419,
    495489, 116567, 116587, 116693, 116713, 121563, 121593, 121687, 121717, 134063, 134093, 134187,
    134217, 135317, 135337, 135443, 135463, 539041, 539111, 539169, 539239, 542789, 542869, 542911,
    542991]

@[expose] def PLc (k : Nat) : List Nat := if k = 2 then PL2 else PL0

@[expose] def E40 : List Nat :=
  [21915, 21945, 21955, 21985, 25035, 25055, 25095, 25115, 79003, 79127, 79503, 79629, 79751, 79877,
    80127, 80251, 80379, 80503, 80877, 81003]

@[expose] def E42 : List Nat :=
  [19002, 19128, 78795, 78855, 116567, 116587, 116693, 116713, 121563, 121593, 121687, 121717,
    134063, 134093, 134187, 134217, 135317, 135337, 135443, 135463]

@[expose] def E4c (k : Nat) : List Nat := if k = 2 then E42 else E40

@[expose] def TPc (k : Nat) : Nat × Nat := if k = 2 then (19002, 116567) else (79003, 79503)

theorem pl_set : ∀ k < 3, (PLc k).length = PC.getD k 0 ∧ (PLc k).Nodup ∧
    ∀ j < PC.getD k 0, (PLc k).contains (f20 (PB.getD k 0) j) = true := by
  decide +kernel

theorem pl_key : ∀ k < 3, ((PLc k).map keyC).Pairwise (· < ·) := by decide +kernel

theorem pl_e4 : ∀ k < 3, ((PLc k).filter fun c => ordK c == 4).filter (normKc K1c K2c) = E4c k := by
  decide +kernel

theorem pl_head : ∀ k < 3, (tpL (E4c k)).head? = some (TPc k) := by decide +kernel

theorem pl_checkP : ∀ k < 4,
    checkPK K1c (RK.getD k (0, 0)).1 (RK.getD k (0, 0)).2 (TPc (if k = 3 then 2 else 0)).1
      (TPc (if k = 3 then 2 else 0)).2 (PLc (if k = 3 then 2 else 0)) (tpL (E4c (if k = 3 then 2 else 0))) =
      true := by
  decide +kernel

theorem pl_set_neg : (!(PL0.set 0 18781).contains (f20 (PB.getD 0 0) 0)) = true := by decide +kernel

theorem pl_checkP_neg : (!checkPK K1c 409405 81126 79003 79503 PL0.tail (tpL E40)) = true := by
  decide +kernel

theorem pl_checkP_neg2 : (!checkPK K1c 409405 81126 79003 79127 PL0 (tpL E40)) = true := by
  decide +kernel

end CertificateChecks.FiveStd

end
