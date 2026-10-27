module

public import Certificates.Kernel.Sporadic.OddCore.SuzRK
public import CFSG.Certificates.Kernel.Spor.RawSound
meta import CFSG.Sporadic.SuzRecog.RootTwistChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzRKR CFSG.Sporadic.SuzRecog.LevelTwoData.rhoHex

#kmisc_hexflat CertificateChecks.KernelSpor.SuzRKR CFSG.Sporadic.SuzRecog.LevelTwoData.rhoHex
  3 1782 11 1

namespace CertificateChecks.KernelSpor.SuzRK

open CFSG.Sporadic.SuzRecog.RootTwistCheck CFSG.Monster.B.Co2.Native

meta def wOf (e : Array Nat) : Nat :=
  let a := CFSG.Sporadic.SuzRecog.RootTwistData.kGenAArr
  let b := CFSG.Sporadic.SuzRecog.RootTwistData.kGenBArr
  let r := CFSG.Sporadic.SuzRecog.LevelTwoData.rhoArr
  let dA := (List.range 1782).find? fun x => e[a[x]!]! != a[e[x]!]!
  let dB := (List.range 1782).find? fun x => e[b[x]!]! != b[e[x]!]!
  let dC := (List.range 1782).find? fun x => e[e[e[x]!]!]! != x
  match dA, dB, dC with
  | some x, _, _ => 4 * x
  | none, some x, _ => 4 * x + 1
  | none, none, some x => 4 * x + 2
  | none, none, none =>
    if eqA 1782 e r then 4 + 3 else if eqA 1782 e (compA 1782 r r) then 8 + 3 else 3

meta def wM : Array (Array Nat) := kEls.map fun e => #[wOf e]

end CertificateChecks.KernelSpor.SuzRK

#kmisc_packarrs CertificateChecks.KernelSpor.SuzRKW CertificateChecks.KernelSpor.SuzRK.wM 32

namespace CertificateChecks.KernelSpor.SuzRKZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CertificateChecks.KernelSpor

@[expose] noncomputable def movK (t g x : Nat) : Bool :=
  bIf(Nat.beq (pg 11 (mask 11) t (pg 11 (mask 11) g x)) (pg 11 (mask 11) g (pg 11 (mask 11) t x)),
    false, true)

@[expose] noncomputable def zK (W : Nat → Nat) (i : Nat) : Bool :=
  strictB (SuzRKT i) (fun t => strictB (W i) (fun w =>
  strictB (Nat.div w (nat_lit 4)) (fun x => strictB (Nat.mod w (nat_lit 4)) (fun c =>
  bAnd(Nat.blt x (nat_lit 1782),
  bIf(Nat.beq c (nat_lit 0), movK t (SuzRKG 0) x,
  bIf(Nat.beq c (nat_lit 1), movK t (SuzRKG 1) x,
  bIf(Nat.beq c (nat_lit 2),
    bIf(Nat.beq (pg 11 (mask 11) t (pg 11 (mask 11) t (pg 11 (mask 11) t x))) x, false, true),
  bIf(Nat.beq x (nat_lit 0), Nat.beq t (pidn 1782 11),
  bIf(Nat.beq x (nat_lit 1), Nat.beq t (SuzRKR.F 0),
    Nat.beq t (pcomp 1782 11 (mask 11) (SuzRKR.F 0) (SuzRKR.F 0))))))))))))

theorem canR : canonK 1782 11 (mask 11) (1782 * 11) (SuzRKR.F 0) = true := by quickRfl

theorem zAll : allN 3456 (zK SuzRKW) = true := by quickRfl

theorem neg_id : Bool.not (zK (fun _ => 3) 5) = true := by quickRfl

theorem neg_comm : Bool.not (zK (fun _ => 0) 0) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzRKZ

end
