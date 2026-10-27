module

public import Certificates.Kernel.Sporadic.Co2Inv.Bind
public import Certificates.Kernel.Sporadic.Co2Inv.Rec0
public import Certificates.Kernel.Sporadic.Co2Inv.Rec1
public import Certificates.Kernel.Sporadic.Co2Inv.Rec2
public import Certificates.Kernel.Sporadic.Co2Inv.Rec3
public import Certificates.Kernel.Sporadic.Co2Inv.Rec4
public import Certificates.Kernel.Sporadic.Co2Inv.Rec5
public import Certificates.Kernel.Sporadic.Co2Inv.Rec6
public import Certificates.Kernel.Sporadic.Co2Inv.Rec7
public import Certificates.Kernel.Sporadic.Co2Inv.Rec8
public import Certificates.Kernel.Sporadic.Co2Inv.Rec9
public import Certificates.Kernel.Sporadic.Co2Inv.Rec10
public import Certificates.Kernel.Sporadic.Co2Inv.Rec11
public import Certificates.Kernel.Sporadic.Co2Inv.Rec12
public import Certificates.Kernel.Sporadic.Co2Inv.Rec13
public import Certificates.Kernel.Sporadic.Co2Inv.Rec14
public import Certificates.Kernel.Sporadic.Co2Inv.Rec15
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelSpor.Co2Inv

open CFSG.KC.Co2InvS CFSG.Sporadic.Co2Inv

theorem recs_all : ∀ k < 262144, recOK E.CF G YT FW 262144 k = true := by
  have h16 : ∀ i < 16, ∀ t < 16384, recOK E.CF G YT FW 262144 (Nat.add (16384 * i) t) = true := by
    intro i hi
    interval_cases i
    exacts [recs0, recs1, recs2, recs3, recs4, recs5, recs6, recs7, recs8, recs9, recs10, recs11,
      recs12, recs13, recs14, recs15]
  intro k hk
  have h := h16 (k / 16384) (by omega) (k % 16384) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (16384 * (k / 16384)) (k % 16384) = k := Nat.div_add_mod k 16384
  rwa [e] at h

theorem head0 : Nat.beq (elemAt E.CF 0) IDP = true := by quickRfl

theorem head1 : Nat.beq (mOf (recAt E.CF 0)) 1 = true := by quickRfl

theorem recsK : Recs E.CF G YT FW sOrder :=
  ⟨recs_all, Nat.eq_of_beq_eq_true head0, Nat.eq_of_beq_eq_true head1, by decide, by decide,
    gens_size, gens_eq⟩

end CertificateChecks.KernelSpor.Co2Inv

end
