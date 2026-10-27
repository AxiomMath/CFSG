module

public import Certificates.Kernel.SporSch.Ru.E64K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.G2Ru7163

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.RuE64 CertificateChecks.KernelSporSch.RuE64
  CertificateChecks.KernelSporSch.G2Ru7164 CFSG.Quasithin.H13.Ch4.G2Ru
open CFSG.KLie.CT (anyN)

@[expose] noncomputable def RAk (i : Nat) : Nat := wK Cf (g2RhoWords.getD i [])

@[expose] noncomputable def wCheck : Bool :=
  (List.range 6).all (fun i => (List.range 6).all fun j =>
      Nat.beq (pc (WG i) (WG j)) (pc (WG j) (WG i))) &&
    (List.range 6).all (fun i => Nat.beq (pc (WG i) (WG i)) pid) &&
    Nat.beq (WG 0) (powK CertificateChecks.KernelSporSch.RuG.C0 10) &&
    (List.range 64).all (fun e => (List.range 6).all fun k => inWK (pc (WG k) (WPk e)))

@[expose] noncomputable def vCheck : Bool :=
  inWK (VG 1) && inWK (VG 2) &&
    (List.range 8).all (fun i => (List.range 8).all fun j =>
      !decide (i < j) || !Nat.beq (VPk i) (VPk j)) &&
    (List.range 8).all (fun e => (List.range 3).all fun k => inVK (pc (VG k) (VPk e)))

@[expose] noncomputable def rhoPt (i j y : Nat) : Nat := ap (pinv (RAk i)) (ap (RAk j) y)

@[expose] noncomputable def rhoCheck : Bool :=
  (List.range 20).all fun i => (List.range 20).all fun j =>
    !decide (i < j) || (List.range 6).any fun k => (List.range 64).all fun e =>
      !Nat.beq (rhoPt i j (ap (WG k) 1)) (ap (WPk e) (rhoPt i j 1)) ||
        !Nat.beq (rhoPt i j (ap (WG k) 0)) (ap (WPk e) (rhoPt i j 0))

@[expose] noncomputable def normB (G E : Nat → Nat) (r m c : Nat) : Bool :=
  allN r fun k => anyN m fun e =>
    bAnd(Nat.beq (evK LR TR c (ap (G k) 1)) (ap (E e) (evK LR TR c 1)),
      Nat.beq (evK LR TR c (ap (G k) 0)) (ap (E e) (evK LR TR c 0)))

@[expose] noncomputable def sCheck : Bool :=
  allN 16384 fun c => bIf(normB WG WPk 6 64 c, normB VG VPk 3 8 c, true)

theorem k7163 : (wCheck && vCheck && rhoCheck && sCheck) = true := by quickRfl

end CertificateChecks.KernelSporSch.G2Ru7163

end
