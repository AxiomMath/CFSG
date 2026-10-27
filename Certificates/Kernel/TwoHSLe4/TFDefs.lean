module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Check

public section

namespace CertificateChecks.KernelTwoHSLe4.TF

open CFSG.EvenSporadicStandard.TwoHS

@[expose] def S (a : R4) : List R4 := sListR a

@[expose] def T (a : R4) : List R4 := tListR a

@[expose] def I (a : R4) : List (R4 × R4) := invPairsR (T a)

theorem tfR_of_traw {a : R4} (h : TRaw (S a) (T a) (I a)) : tfR a = true := by
  change decide (TRaw (sListR a) (tListR a) (invPairsR (tListR a))) = true
  exact decide_eq_true h

end CertificateChecks.KernelTwoHSLe4.TF
