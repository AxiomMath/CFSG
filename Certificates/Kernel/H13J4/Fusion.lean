
module

public import Certificates.Kernel.SporSch.J4S.Eta
public import Certificates.Kernel.SporSch.J4S.InvP
public import CFSG.Quasithin.H13.J4ClassCheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelH13.J4Fusion

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta
open CertificateChecks.KernelSporSch.J4InvP
open CFSG.Quasithin.H13.J4

@[expose] noncomputable def pmul (p q : Nat × Nat) : Nat × Nat := (mulJ c rm p.1 q.1, mulJ c rm q.2 p.2)

@[expose] noncomputable def pinv (p : Nat × Nat) : Nat × Nat := (p.2, p.1)

@[expose] noncomputable def ppow (p : Nat × Nat) (e : Nat) : Nat × Nat :=
  (powJ c rm one p.1 e, powJ c rm one p.2 e)

@[expose] def POK (P : Pair) (p : Nat × Nat) : Prop := PairOK P p.1 p.2

theorem pmul_ok {P Q : Pair} {p q : Nat × Nat} (hP : POK P p) (hQ : POK Q q) :
    POK (mulP P Q) (pmul p q) := mulP_ok J4Real.hK hP hQ

theorem pinv_ok {P : Pair} {p : Nat × Nat} (hP : POK P p) : POK (invP P) (pinv p) := invP_ok hP

theorem ppow_ok {P : Pair} {p : Nat × Nat} (hP : POK P p) (e : Nat) : POK (powP P e) (ppow p e) :=
  powP_ok J4Real.hK hP e

@[expose] noncomputable def wAB (w : List Int) : Nat × Nat :=
  (wFK c rm one A A B Bi w one, wSK c rm one A A B Bi w one)

@[expose] noncomputable def wXY (w : List Int) : Nat × Nat :=
  (wFK c rm one (R 1) (R 10) (R 2) (R 11) w one, wSK c rm one (R 1) (R 10) (R 2) (R 11) w one)

theorem lettersOK_spec {w : List Int} (h : lettersOK w = true) :
    ∀ l ∈ w, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by
  intro l hl
  simp only [lettersOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  have := h l hl
  tauto

theorem letters_ok : lettersOK Native.uLetters = true ∧ lettersOK Native.vLetters = true :=
  ⟨by decide +kernel, by decide +kernel⟩

@[expose] noncomputable def uK : Nat × Nat := wAB Native.uLetters
@[expose] noncomputable def vK : Nat × Nat := wAB Native.vLetters
@[expose] noncomputable def dK : Nat × Nat := pmul (pmul (pmul (pinv vK) uK) vK) uK
@[expose] noncomputable def tK : Nat × Nat := ppow dK 22

theorem uK_ok : POK uP uK := wordP_ok' J4Real.hK pA pB _ (lettersOK_spec letters_ok.1)
theorem vK_ok : POK vP vK := wordP_ok' J4Real.hK pA pB _ (lettersOK_spec letters_ok.2)
theorem dK_ok : POK dP dK := pmul_ok (pmul_ok (pmul_ok (pinv_ok vK_ok) uK_ok) vK_ok) uK_ok
theorem tK_ok : POK tP tK := ppow_ok dK_ok 22

@[expose] noncomputable def e2K : Nat × Nat := ppow (wXY e2Word) 6
@[expose] noncomputable def e3K : Nat × Nat :=
  pmul (prodFK c rm one (ef 1096), prodSK c rm one (es 1096)) (R 1, R 10)
@[expose] noncomputable def zK : Nat × Nat := (E 1, E 25)
@[expose] noncomputable def cnjK (g e : Nat × Nat) (k : Nat) : Nat × Nat :=
  pmul g (ppow (pmul (pmul (pmul (pinv g) tK) g) e) k)

theorem e2K_ok : POK e2P e2K :=
  ppow_ok (p := wXY e2Word) (wordP_ok' J4Real.hK pX pY e2Word (by decide)) 6
theorem e3K_ok : POK e3P e3K := pmul_ok (etaP_ok 1096) pX
theorem zK_ok : POK Zn zK := pZ

theorem cnjK_ok {G E : Pair} {g e : Nat × Nat} (hG : POK G g) (hE : POK E e) (k : Nat) :
    POK (cnjP G E k) (cnjK g e k) :=
  pmul_ok hG (ppow_ok (pmul_ok (pmul_ok (pmul_ok (pinv_ok hG) tK_ok) hG) hE) k)

@[expose] noncomputable def fusK (c e : Nat × Nat) : Bool := Nat.beq (pmul (pmul (pinv c) tK) c).1 e.1

@[expose] noncomputable def fus1 : Bool := fusK (cnjK (pmul (B, Bi) (A, A)) zK 3) zK
@[expose] noncomputable def fus2 : Bool := fusK (cnjK (pmul (A, A) (B, Bi)) e2K 6) e2K
@[expose] noncomputable def fus3 : Bool := fusK (cnjK (one, one) e3K 6) e3K

theorem fus1_ok : fus1 = true := by quickRfl
theorem fus2_ok : fus2 = true := by quickRfl
theorem fus3_ok : fus3 = true := by quickRfl

theorem conjEqP_of {C E : Pair} {c e : Nat × Nat} (hC : POK C c) (hE : POK E e)
    (h : fusK c e = true) : conjEqP C E = true := by
  have m := pmul_ok (pmul_ok (pinv_ok hC) tK_ok) hC
  have h1 := m.1
  have h2 := hE.1
  have eq : (mulP (mulP (invP C) tP) C).1 = E.1 :=
    enc_inj h1.1 h2.1 (by rw [h1.2, h2.2]; exact Nat.eq_of_beq_eq_true h)
  change (O.eq (mulP (mulP (invP C) tP) C).1 E.1) = true
  change ((mulP (mulP (invP C) tP) C).1 == E.1) = true
  rw [eq]
  exact beq_self_eq_true _

theorem fusionChecks_true : fusionChecks = true := by
  have hBA : POK (mulP Bn An) (pmul (B, Bi) (A, A)) := pmul_ok pB pA
  have hAB : POK (mulP An Bn) (pmul (A, A) (B, Bi)) := pmul_ok pA pB
  have h1' := conjEqP_of (cnjK_ok hBA zK_ok 3) zK_ok fus1_ok
  have h2' := conjEqP_of (cnjK_ok hAB e2K_ok 6) e2K_ok fus2_ok
  have h3' := conjEqP_of (cnjK_ok (g := (one, one)) (oneP_ok J4Real.hK) e3K_ok 6) e3K_ok fus3_ok
  unfold fusionChecks
  rw [h1', h2', h3']
  rfl

end CertificateChecks.KernelH13.J4Fusion

end
