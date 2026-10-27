module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Lists
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CertificateChecks.KernelTwoHSLe4.S9

open CFSG.EvenSporadicStandard.TwoHS CFSG.KC.Enum

@[expose] def rl (l : List ℕ) : R4 :=
  ⟨l.getD 0 0 % 4, l.getD 1 0 % 4, l.getD 2 0 % 4, l.getD 3 0 % 4, l.getD 4 0 % 4,
    l.getD 5 0 % 4, l.getD 6 0 % 4, l.getD 7 0 % 4, l.getD 8 0 % 4, l.getD 9 0 % 4,
    l.getD 10 0 % 4, l.getD 11 0 % 4, l.getD 12 0 % 4, l.getD 13 0 % 4, l.getD 14 0 % 4,
    l.getD 15 0 % 4⟩

@[expose] def genL (l : ℕ) : R4 := if l = 0 then rl gamma1Data else rl gamma2Data

@[expose] def wordR (w : List ℕ) : R4 := w.foldl (fun a l => rmul a (genL l)) R4.one

@[expose] noncomputable def wdec (R : ℕ) : List ℕ :=
  (List.range (pg 6 63 R 0)).map fun i => pg 6 63 R (i + 1)

@[expose] def shatA : List R4 := (shatData.map rl).take 12

@[expose] def shatB : List R4 := (shatData.map rl).drop 12

@[expose] def subChunk (j : ℕ) : Bool :=
  shatA.sublists.all fun z => subCheck (z ++ shatB.sublists.getD j [])

end CertificateChecks.KernelTwoHSLe4.S9

end
