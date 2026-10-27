module

public import Certificates.Kernel.J4Q.LocM
public import Certificates.Data.Kernel.J4Q.Words26
public import Certificates.Data.J4Ov.WordsMax
import Certificates.Kernel.J4Q.Strs
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Ov.MT4204 CFSG.Quasithin.J4Ov.maxToTwo
#j4q_strs CFSG.KD.J4Ov.MF4204 CFSG.Quasithin.J4Ov.maxFromTwo

namespace CertificateChecks.KernelJ4Ov

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4Ov CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2
  CertificateChecks.KernelJ4Q

theorem maxToTwo_strs4204 : CFSG.Quasithin.J4Ov.maxToTwo =
    [String.ofList MT4204.s0, String.ofList MT4204.s1, String.ofList MT4204.s2,
      String.ofList MT4204.s3, String.ofList MT4204.s4, String.ofList MT4204.s5,
      String.ofList MT4204.s6] := MT4204.eq

theorem maxFromTwo_strs4204 : CFSG.Quasithin.J4Ov.maxFromTwo =
    [String.ofList MF4204.s0, String.ofList MF4204.s1, String.ofList MF4204.s2,
      String.ofList MF4204.s3, String.ofList MF4204.s4, String.ofList MF4204.s5,
      String.ofList MF4204.s6] := MF4204.eq

@[expose] noncomputable def mt4204 : List (List Int) :=
  [lettersAZ MT4204.s0, lettersAZ MT4204.s1, lettersAZ MT4204.s2, lettersAZ MT4204.s3,
    lettersAZ MT4204.s4, lettersAZ MT4204.s5, lettersAZ MT4204.s6]

@[expose] noncomputable def mf4204 : List (List Int) :=
  [lettersAZ MF4204.s0, lettersAZ MF4204.s1, lettersAZ MF4204.s2, lettersAZ MF4204.s3,
    lettersAZ MF4204.s4, lettersAZ MF4204.s5, lettersAZ MF4204.s6]

@[expose] noncomputable def tgt4204 : List Nat := [1, 3, 4, 5, 6]

@[expose] noncomputable def max4204K (l k : Nat) (w : List Int) : Bool :=
  Nat.beq (wordVJ rm one [L0, L1, L2, getN one MLIs (Nat.sub l 1)]
      [L0i, L1i, L2i, getN one MLs (Nat.sub l 1)] w
      (pathVK rm one [A, B] (repPaths.getD k []) (v2N rootV)))
    (v2N rootV)

@[expose] noncomputable def ch4204K (t : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (max4204K 2 (getN 0 tgt4204 (Nat.sub t 5)) (mf4204.getD (getN 0 tgt4204 (Nat.sub t 5)) []))
    (max4204K (getN 0 tgt4204 t) 2 (mt4204.getD (getN 0 tgt4204 t) []))
    (Nat.blt t 5)

#j4q_all CFSG.KD.J4Ov.ch4204 CertificateChecks.KernelJ4Ov.ch4204K 10

theorem ch4204_neg_l : notB (max4204K 1 2 (mt4204.getD 3 [])) = true := by quickRfl

theorem ch4204_neg_w : notB (max4204K 2 4 ((mf4204.getD 4 []).dropLast)) = true := by quickRfl

end CertificateChecks.KernelJ4Ov

end
