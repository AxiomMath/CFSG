module

public import Certificates.Kernel.SporSch.Ly.GenSeven
public import Certificates.Kernel.SporSch.Ly.BSData
public import Certificates.Data.Kernel.SporSch.LySeven
public import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kly_sev CertificateChecks.KernelSporSch.LySv

#ks_chars CertificateChecks.KernelSporSch.LySWT CFSG.Sporadic.LySchreier.Native.strongWordsTxt

#ks_chars CertificateChecks.KernelSporSch.LyRDT CFSG.Sporadic.LySchreier.Native.rootDigitsTxt

namespace CertificateChecks.KernelSporSch.LySv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CertificateChecks.KernelSporSch.LyBS

@[expose] noncomputable def AFx (k i : Nat) : Nat := nIf(Nat.blt i k, AF i, ONE)

@[expose] noncomputable def AIx (k i : Nat) : Nat := nIf(Nat.blt i k, AI i, ONE)

end CertificateChecks.KernelSporSch.LySv

#kly_sevchain CertificateChecks.KernelSporSch.LySv 2 16
#kly_sevchain CertificateChecks.KernelSporSch.LySv 3 16
#kly_sevchain CertificateChecks.KernelSporSch.LySv 4 16
#kly_sevchain CertificateChecks.KernelSporSch.LySv 5 16
#kly_sevchain CertificateChecks.KernelSporSch.LySv 6 16

namespace CertificateChecks.KernelSporSch.LySv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySev
open CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS

theorem nas : Nat.beq nAS 7 = true := by quickRfl
theorem bb : Nat.beq (mul B B4) ONE = true := by quickRfl
theorem vAF : allN 7 (fun i => bAnd(vld (AF i), vld (AI i))) = true := by quickRfl
theorem iAF : allN 7 (fun i => Nat.beq (mul (AF i) (AI i)) ONE) = true := by quickRfl
theorem a01 : bAnd(Nat.beq (AF 0) A, bAnd(Nat.beq (AI 0) A, bAnd(Nat.beq (AF 1) B,
    Nat.beq (AI 1) B4))) = true := by quickRfl

theorem k2 : bAnd(Nat.beq (K2 0) ONE, bAnd(Nat.beq (K2 K2.m) (AF 2),
    Nat.ble SW2.length (Nat.mul K2.m 16))) = true := by quickRfl
theorem k3 : bAnd(Nat.beq (K3 0) ONE, bAnd(Nat.beq (K3 K3.m) (AF 3),
    Nat.ble SW3.length (Nat.mul K3.m 16))) = true := by quickRfl
theorem k4 : bAnd(Nat.beq (K4 0) ONE, bAnd(Nat.beq (K4 K4.m) (AF 4),
    Nat.ble SW4.length (Nat.mul K4.m 16))) = true := by quickRfl
theorem k5 : bAnd(Nat.beq (K5 0) ONE, bAnd(Nat.beq (K5 K5.m) (AF 5),
    Nat.ble SW5.length (Nat.mul K5.m 16))) = true := by quickRfl
theorem k6 : bAnd(Nat.beq (K6 0) ONE, bAnd(Nat.beq (K6 K6.m) (AF 6),
    Nat.ble SW6.length (Nat.mul K6.m 16))) = true := by quickRfl

theorem lines : linesK LySWT.chars LS = true := by quickRfl
theorem sw : LS.drop 2 = [SW2, SW3, SW4, SW5, SW6] := by decide
theorem lsLen : LS.length = 7 := by decide

theorem digs : digK LyRDT.chars DG nDG = true := by quickRfl
theorem ndg : nDG = 826 := by decide

theorem vUP : vld UP = true := by quickRfl
theorem upOK : allN 111 (fun i => allN 111 (fun j => Nat.beq fld(UP, Nat.add (Nat.mul 1332 i)
    (Nat.mul 12 j), 4095) (nIf(Nat.blt j 7, fld(DG, Nat.mul 4 (Nat.add (Nat.mul 111 j) i), 15), 0))))
    = true := by quickRfl

@[expose] noncomputable def rOK (X : Nat) (R : Array Nat) : Bool :=
  strictB (mul X UP) (fun XU => allN 49 (fun t =>
    Nat.beq fld(XU, Nat.add (Nat.mul 1332 (Nat.div t 7)) (Nat.mul 12 (Nat.mod t 7)), 4095) (R[t]!)))

@[expose] noncomputable def sOK (X : Nat) : Bool :=
  strictB (mul X UP) (fun XU => Nat.beq XU (mul UP (Nat.land XU (Nat.sub (2 ^ 9324) 1))))

theorem rA2 : rOK (AF 2) (RA[0]!) = true := by quickRfl
theorem rA3 : rOK (AF 3) (RA[1]!) = true := by quickRfl
theorem rA4 : rOK (AF 4) (RA[2]!) = true := by quickRfl
theorem rA5 : rOK (AF 5) (RA[3]!) = true := by quickRfl
theorem rA6 : rOK (AF 6) (RA[4]!) = true := by quickRfl
theorem sA2 : sOK (AF 2) = true := by quickRfl
theorem sA3 : sOK (AF 3) = true := by quickRfl
theorem sA4 : sOK (AF 4) = true := by quickRfl
theorem sA5 : sOK (AF 5) = true := by quickRfl
theorem sA6 : sOK (AF 6) = true := by quickRfl

theorem vV : bAnd(vld V, bAnd(vld VI, vld TT)) = true := by quickRfl
theorem vw : Nat.beq (wordR 5 12 1332 111 8 L H CM RM GS GSI ONE (transporterWord ())) V = true := by
  quickRfl
theorem vvi : Nat.beq (mul V VI) ONE = true := by quickRfl
theorem tt : Nat.beq (mul (mul VI A) V) TT = true := by quickRfl
theorem rT : rOK TT RT = true := by quickRfl

end CertificateChecks.KernelSporSch.LySv

end
