
module

public import Certificates.Kernel.J2Cover.ExtChains
public import Certificates.Kernel.J2Cover.K21
public import Certificates.Kernel.J2Cover.Orb
meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalData
public import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelJ2Cover.FU 9 CFSG.ComponentClassification.J2Cover.External.fusionArr

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText TxtExternal
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.External
open CFSG.ComponentClassification.J2Cover.Models (bArr bInvArr letterArr betaArr)

theorem allL_spec {f : Nat → Bool} : ∀ {L : List Nat}, allL f L = true → ∀ x ∈ L, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | y :: L, h, x, hx => by
    have h' : bAnd(f y, allL f L) = true := h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact allL_spec h2 x hx

theorem commA_of {t r : Array Nat} {T R : Nat} (ht : t = unpack 315 9 T) (hr : r = unpack 315 9 R)
    (cT : CnN 315 9 T) (cR : CnN 315 9 R)
    (h : Nat.beq (pcomp 315 9 (mask 9) T R) (pcomp 315 9 (mask 9) R T) = true) :
    commA t r = true := by
  unfold commA
  rw [ht, hr, compA_unpackN cT cR, compA_unpackN cR cT, eqA_unpackN (canon_pcN cT cR)
    (canon_pcN cR cT)]
  exact h

theorem hOUM : CFSG.ComponentClassification.J2Cover.Models.outerU = unpack 315 9 OU :=
  arrBind_sound (by quickRfl)

@[expose] noncomputable def BB : Nat :=
  pcomp 315 9 (mask 9) (PA.S 1) (pcomp 315 9 (mask 9) OU (PA.SI 1))

theorem bArr_eq : bArr = unpack 315 9 BB := by
  have e : letterArr 1 = unpack 315 9 (PA.S 1) := by
    unfold letterArr
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide : ¬ (1 : Nat) = 0)), betaArr_eq]
  have c1 : CnN 315 9 (PA.S 1) := by quickRfl
  have c2 : CnN 315 9 (PA.SI 1) := by quickRfl
  have c3 : CnN 315 9 OU := by quickRfl
  unfold bArr bInvArr
  rw [e, (invEqK_sound (allN_spec perm 1 (by omega))).1, hOUM, compA_unpackN c3 c2,
    compA_unpackN c1 (canon_pcN c3 c2)]
  rfl

theorem fC_S (j : Nat) (hj : j < 4) : fixCStrong[j]! = unpack 315 9 (FC.S j) :=
  fC_binds.2.2.2.2.1 j hj

theorem fD_S (j : Nat) (hj : j < 2) : fixDStrong[j]! = unpack 315 9 (FD.S j) :=
  fD_binds.2.2.2.2.1 j hj

theorem fW_S (j : Nat) (hj : j < 2) : fixWStrong[j]! = unpack 315 9 (FW.S j) :=
  fW_binds.2.2.2.2.1 j hj

theorem inC_of {t : Array Nat} {G : Nat} (ht : t = unpack 315 9 G)
    (hz : Nat.beq (Nat.shiftRight G (315 * 9)) 0 = true)
    (hr : allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315) = true)
    (hs : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) FC.LR FC.TRI FC.BP 2 0 G = true) :
    inC t = true :=
  siftK_soundR fC_binds fC_perm FC.hl ht (Nat.eq_of_beq_eq_true hz) hr hs

theorem inD_of {t : Array Nat} {G : Nat} (ht : t = unpack 315 9 G)
    (hz : Nat.beq (Nat.shiftRight G (315 * 9)) 0 = true)
    (hr : allN 315 (fun i => Nat.blt (pg 9 (mask 9) G i) 315) = true)
    (hs : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) FD.LR FD.TRI FD.BP 1 0 G = true) :
    inD t = true :=
  siftK_soundR fD_binds fD_perm FD.hl ht (Nat.eq_of_beq_eq_true hz) hr hs

theorem chainC : CFSG.ComponentClassification.J2Cover.External.chainCheck = true := by
  have p0 : inP fixCStrong[0]! = true :=
    inP_of (fC_S 0 (by omega)) (by quickRfl) (by quickRfl) (by quickRfl)
  have p1 : inP fixCStrong[1]! = true :=
    inP_of (fC_S 1 (by omega)) (by quickRfl) (by quickRfl) (by quickRfl)
  have b0 : commA fixCStrong[0]! bArr = true :=
    commA_of (fC_S 0 (by omega)) bArr_eq (by quickRfl) (by quickRfl) (by quickRfl)
  have b1 : commA fixCStrong[1]! bArr = true :=
    commA_of (fC_S 1 (by omega)) bArr_eq (by quickRfl) (by quickRfl) (by quickRfl)
  have c0 : inC fixDStrong[0]! = true :=
    inC_of (fD_S 0 (by omega)) (by quickRfl) (by quickRfl) (by quickRfl)
  have c1 : inC fixDStrong[1]! = true :=
    inC_of (fD_S 1 (by omega)) (by quickRfl) (by quickRfl) (by quickRfl)
  have d0 : inD fixWStrong[0]! = true :=
    inD_of (fW_S 0 (by omega)) (by quickRfl) (by quickRfl) (by quickRfl)
  have d1 : inD fixWStrong[1]! = true :=
    inD_of (fW_S 1 (by omega)) (by quickRfl) (by quickRfl) (by quickRfl)
  unfold CFSG.ComponentClassification.J2Cover.External.chainCheck
  rw [fC_chain.1, fC_chain.2, p0, p1, b0, b1, fD_chain.1, fD_chain.2, c0, c1, fW_chain.1,
    fW_chain.2, d0, d1]
  rfl

end CertificateChecks.KernelJ2Cover

end
