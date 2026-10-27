module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernelData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4PrimeKernelData
public import Certificates.Kernel.J4M2.C12603Checks
public import Certificates.Kernel.SporSch.J4S.RealK
public import CFSG.Certificates.Kernel.SporSch.J4S11Sound
public import CFSG.Certificates.Kernel.SporSch.J4SFormSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4PK

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.KS.SporSch.J4PK
  CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native

theorem hK : Consts c rm one pad t0 t1 t2 t3 t4 t5 t6 := CertificateChecks.KernelJ4Q.hK

theorem pAn : PairOK An A A :=
  ⟨CertificateChecks.KernelSporSch.J4Real.hA, CertificateChecks.KernelSporSch.J4Real.hA⟩

theorem pBn : PairOK Bn B Bi :=
  ⟨CertificateChecks.KernelSporSch.J4Real.hB, CertificateChecks.KernelSporSch.J4Real.hB3⟩

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.J4Q.strictB y k = k y := by
  cases y <;> rfl

theorem andB_iff {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem zero_enc : WfN (Array.replicate 112 0) ∧ encN (Array.replicate 112 0) = 0 :=
  ⟨⟨Array.size_replicate, fun i hi => by
    rw [getElem!_pos _ i (by rw [Array.size_replicate]; exact hi), Array.getElem_replicate]
    exact Nat.two_pow_pos _⟩, by decide +kernel⟩

theorem poly_enc {X : Array Nat} (hX : WfN X) : ∀ es : List Nat, (∀ e ∈ es, e < 2 ^ 7) →
    WfN (polyRows X es) ∧ encN (polyRows X es) = polyK c rm one (encN X) es
  | [], _ => zero_enc
  | e :: es, h => by
    have ih := poly_enc hX es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    have hp := powB_enc hK 7 e hX (h e List.mem_cons_self)
    have x := xor_enc hp.1 ih.1
    have e1 : polyRows X (e :: es) = xorRows112 (O.pow X e) (polyRows X es) := rfl
    rw [e1]
    refine ⟨x.1, ?_⟩
    rw [x.2, hp.2, ih.2]
    rfl

theorem case_ok (C : PrimeKerCase) {P Pi R : Nat}
    (hw : ∀ l ∈ C.word, l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2) (he : C.exp < 2 ^ 65)
    (hr : C.order < 2 ^ 7) (hes : ∀ e ∈ C.exps, e < 2 ^ 7) (hk : C.k ≤ 112)
    (hP : WfN C.P ∧ encN C.P = P) (hPi : WfN C.Pinv ∧ encN C.Pinv = Pi)
    (hR : WfN C.R ∧ encN C.R = R) (h : chk C P Pi R = true) : primeKerCaseOK C = true := by
  have hX : WfN (primeKerElt C).1 ∧ encN (primeKerElt C).1 = eltK c rm one A B Bi C.word C.exp :=
    (powP_okB hK (wordP_ok' hK pAn pBn C.word hw) (fuel := 65) he).1
  simp only [chk, caseK, strictB_eq, andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  unfold primeKerCaseOK
  rw [Bool.and_eq_true]
  constructor
  · have m := powB_enc hK 7 C.order hX.1 hr
    have i := CFSG.KS.SporSch.J4B.id_enc hK
    have e1 : encN (O.pow (primeKerElt C).1 C.order) = encN (idRows 112) := by
      rw [m.2, hX.2, i.2]
      exact Nat.eq_of_beq_eq_true h1
    have e2 : O.pow (primeKerElt C).1 C.order = idRows 112 := CFSG.KS.SporSch.J4B.enc_inj m.1 i.1 e1
    change (O.pow (primeKerElt C).1 C.order == idRows 112) = true
    rw [e2]
    exact beq_self_eq_true _
  · have hp := poly_enc hX.1 C.exps hes
    have i := CFSG.KS.SporSch.J4B.id_enc hK
    have hg := xor_enc hp.1 i.1
    have h2' : fixK c rm one (encN (xorRows112 (polyRows (primeKerElt C).1 C.exps) (idRows 112)))
        (encN C.P) (encN C.Pinv) (encN C.R) C.k = true := by
      rw [hg.2, hp.2, i.2, hX.2, hP.2, hPi.2, hR.2]
      exact h2
    exact fixK_sound hK hg.1 hP.1 hPi.1 hR.1 hk h2'

theorem ok5 : primeKerCaseOK kerCase5 = true :=
  case_ok kerCase5 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (pack_enc p5) (pack_enc i5) (pack_enc r5) c5

theorem ok7 : primeKerCaseOK kerCase7 = true :=
  case_ok kerCase7 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (pack_enc p7) (pack_enc i7) (pack_enc r7) c7

theorem ok23 : primeKerCaseOK kerCase23 = true :=
  case_ok kerCase23 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (pack_enc p23) (pack_enc i23) (pack_enc r23) c23

theorem ok29 : primeKerCaseOK kerCase29 = true :=
  case_ok kerCase29 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (CFSG.KS.SporSch.J4B.id_enc hK) (CFSG.KS.SporSch.J4B.id_enc hK) (CFSG.KS.SporSch.J4B.id_enc hK) c29

theorem ok31 : primeKerCaseOK kerCase31 = true :=
  case_ok kerCase31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (pack_enc p31) (pack_enc i31) (pack_enc r31) c31

theorem ok37 : primeKerCaseOK kerCase37 = true :=
  case_ok kerCase37 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (pack_enc p37) (pack_enc i37) (pack_enc r37) c37

theorem ok43 : primeKerCaseOK kerCase43 = true :=
  case_ok kerCase43 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (CFSG.KS.SporSch.J4B.id_enc hK) (CFSG.KS.SporSch.J4B.id_enc hK) (CFSG.KS.SporSch.J4B.id_enc hK) c43

theorem primeKerOK_ok : primeKerOK = true := by
  unfold primeKerOK
  rw [ok5, ok7, ok23, ok29, ok31, ok37, ok43]
  rfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier in
theorem c12603 : primeKerOK = true := primeKerOK_ok

end CertificateChecks.KernelJ4PK

end
