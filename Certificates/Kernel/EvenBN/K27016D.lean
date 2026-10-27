module

public import Certificates.Data.TitsAschbacherSecFour
public import Certificates.Kernel.EvenBN.CNtAux
public import Certificates.Kernel.EvenBN.Lists
public import Certificates.Kernel.EvenBN.K27016B
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27016

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits
open CertificateChecks.KernelSpor CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsInv
open CertificateChecks.KernelEvenBN Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def U1 : Nat := wP TitsN.S u1Word
@[expose] noncomputable def U2 : Nat := wP TitsN.S u2Word
@[expose] noncomputable def U3 : Nat := pc U1 U2

@[expose] noncomputable def QL : List Nat := qWords.map (wP TitsN.S)

@[expose] noncomputable def TU : List Nat :=
  [pidn 1755 11, U1, U2, U3, TitsT, pc TitsT U1, pc TitsT U2, pc TitsT U3]

@[expose] noncomputable def sqE (k : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c (pidn 1755 11))
    (fun _ ih c => bIf(Nat.beq c (pidn 1755 11), true, strictB (pc c c) ih)) k

@[expose] noncomputable def TUL : List Nat :=
  [pidn 1755 11, U1L, U2L, U3L, TitsT, pc TitsT U1L, pc TitsT U2L, pc TitsT U3L]

@[expose] noncomputable def bT (g : Nat → Nat) (y z : Nat) : Bool :=
  baseTw TitsN.BP 5 g (pgR y) (pgR z)

@[expose] noncomputable def cKG (g : Nat → Nat) (Z1 Z2 Z3 R1 R2 R3 x : Nat) : Bool :=
  (bT g U1L Z1 || (bT g U1L Z2 || bT g U1L Z3)) &&
    (bT g U2L Z1 || (bT g U2L Z2 || bT g U2L Z3)) &&
    (!(bT g Q1L R1 && (bT g Q2L R2 && bT g Q3L R3)) || TUL.any (Nat.beq x)) &&
    (!(bT g U1L Z1 && bT g U2L Z2) || sqE 10 x)

@[expose] noncomputable def cKc (k : Nat) : Bool :=
  cKG (gptC TitsN.LR TitsN.TR k) U1L U2L U3L Q1L Q2L Q3L (PN k) &&
    cKG (gptC TitsN.LR TitsN.TR k) AU1 AU2 AU3 AQ1 AQ2 AQ3 (pc (TAux.F 0) (PN k))

end CertificateChecks.Batch27016

end
