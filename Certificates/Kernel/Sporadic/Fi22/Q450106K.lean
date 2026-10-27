module

public import Certificates.Kernel.Sporadic.Fi22.E2065
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import Certificates.Kernel.Sporadic.Fi22.X2069Final
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBQCheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Q450106

meta def qM : Array (Array Nat) :=
  let S : Array (Array Nat) := Array.ofFn (n := 10) fun h =>
    CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB.genArr h
  let Si := S.map (CFSG.Monster.B.Co2.Native.invCand 3510)
  Array.ofFn (n := 10) fun j => CFSG.Monster.B.Co2.Native.wordA 3510 S Si
    (CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB.qWords.getD j [])

end CertificateChecks.KernelSpor.Q450106

#kmisc_packarrs CertificateChecks.KernelSpor.Q450106.QD CertificateChecks.KernelSpor.Q450106.qM 12

namespace CertificateChecks.KernelSpor.Q450106

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
open CertificateChecks.KernelSpor

@[expose] noncomputable def cl (h : Nat) : Nat := nIf(Nat.blt h (nat_lit 9), Nat.add (nat_lit 19) h, nat_lit 79)

@[expose] noncomputable def CG (h : Nat) : Nat := Fi22CentT.L (cl h)

@[expose] noncomputable def CGI (h : Nat) : Nat := Fi22E2065.CI (cl h)

@[expose] noncomputable def T : Nat := Fi22ExtT.L (nat_lit 22)

@[expose] noncomputable def ID : Nat := pidn 3510 12

@[expose] noncomputable def tp (b : Bool) : Nat := Bool.rec (motive := fun _ => Nat) ID T b

@[expose] noncomputable def monL (v : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) ID
    (fun i _ acc => strictN acc (fun a => Bool.rec (motive := fun _ => Nat) a
      (Fi22X.c (QD i) a) (Nat.testBit v i))) l

@[expose] def L10 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

@[expose] noncomputable def nfK (code : Nat) : Nat :=
  Fi22X.c (tp (Nat.testBit code 10)) (monL code L10)

@[expose] noncomputable def qK : Bool :=
  Fi22X.cn T && Fi22X.cn ID &&
  allN 10 (fun h => bAnd(permOK 3510 12 (mask 12) (3510 * 12) (CG h) (CGI h),
    bAnd(Fi22X.cn (CG h), Fi22X.cn (CGI h)))) &&
  allN 10 (fun j => bAnd(lettersK 10 (qWords.getD j []), bAnd(Fi22X.cn (QD j),
    Nat.beq (wordK 3510 12 (mask 12) ID CG CGI (qWords.getD j [])) (QD j))))

@[expose] noncomputable def relK : Bool :=
  Nat.beq (Fi22X.c T T) ID && Bool.not (Nat.beq T ID) &&
  allN 10 (fun j => bAnd(Nat.beq (Fi22X.c T (QD j)) (Fi22X.c (QD j) T),
    Nat.beq (Fi22X.c (QD j) (QD j)) ID))

@[expose] noncomputable def commK (i : Nat) : Bool :=
  allN 10 (fun j => Nat.beq (Fi22X.c (QD i) (QD j))
    (Fi22X.c (Fi22X.c (QD j) (QD i)) (tp (cBit i j))))

@[expose] noncomputable def conjK (k : Nat) : Bool :=
  allN 10 (fun j => Nat.beq (Fi22X.c (Fi22X.c (CG k) (QD j)) (CGI k))
    (nfK (actCodes.getD (10 * k + j) 0)))

@[expose] noncomputable def centK : Bool :=
  allN 10 (fun k => Nat.beq (Fi22X.c (CG k) T) (Fi22X.c T (CG k)))

theorem q_ok : qK = true := by quickRfl
theorem rel_ok : relK = true := by quickRfl
theorem cent_ok : centK = true := by quickRfl
theorem comm0 : commK 0 = true := by quickRfl
theorem comm1 : commK 1 = true := by quickRfl
theorem comm2 : commK 2 = true := by quickRfl
theorem comm3 : commK 3 = true := by quickRfl
theorem comm4 : commK 4 = true := by quickRfl
theorem comm5 : commK 5 = true := by quickRfl
theorem comm6 : commK 6 = true := by quickRfl
theorem comm7 : commK 7 = true := by quickRfl
theorem comm8 : commK 8 = true := by quickRfl
theorem comm9 : commK 9 = true := by quickRfl
theorem conj0 : conjK 0 = true := by quickRfl
theorem conj1 : conjK 1 = true := by quickRfl
theorem conj2 : conjK 2 = true := by quickRfl
theorem conj3 : conjK 3 = true := by quickRfl
theorem conj4 : conjK 4 = true := by quickRfl
theorem conj5 : conjK 5 = true := by quickRfl
theorem conj6 : conjK 6 = true := by quickRfl
theorem conj7 : conjK 7 = true := by quickRfl
theorem conj8 : conjK 8 = true := by quickRfl
theorem conj9 : conjK 9 = true := by quickRfl

end CertificateChecks.KernelSpor.Q450106

end
