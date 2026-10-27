module

public import Certificates.Kernel.LocalComp.J2Std.Std
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.J2StdOrb
open CFSG.ComponentClassification.RankTwoClassical.J2Std

@[expose] public noncomputable def FP : Nat := pkA 9 j2A4F

@[expose] public noncomputable def crK (k : Nat) : Bool :=
  allN L.ng (fun l => (List.range L.N).any (fun i => Nat.beq (cj (CR.G k) (L.G l)) (L.T i)))

@[expose] public noncomputable def ccK (k : Nat) : Bool :=
  allN CR.ng (fun l => (List.range L.N).any (fun i => Nat.beq (cmt (CR.G k) (CR.G l)) (L.T i)))

@[expose] public noncomputable def c3Sl (s : Nat) : Bool :=
  allN 6 (fun d => (fun p => (!(Nat.beq (pw p 5) (pidn 315 9))) || Nat.beq p (pidn 315 9))
    (C3.T (Nat.add (Nat.mul 6 s) d)))

end CertificateChecks.KernelLC.J2Std

public section

set_option maxRecDepth 400000

#kss_each CertificateChecks.KernelLC.J2Std.OCR CertificateChecks.KernelLC.J2Std.crK 4
#kss_each CertificateChecks.KernelLC.J2Std.OCC CertificateChecks.KernelLC.J2Std.ccK 4
#kss_each CertificateChecks.KernelLC.J2Std.OC3 CertificateChecks.KernelLC.J2Std.c3Sl 6

namespace CertificateChecks.KernelLC.J2Std

open CFSG.KC.Enum CFSG.KC.BfsPin CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.J2StdOrb
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Certificates.Native
open CFSG.ComponentClassification.RankTwoClassical.J2Std CertificateChecks.KernelJ2Cover
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (keyPts okA inCert)
open CFSG.Monster.B.Mathieu (powArr)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem hF : j2A4F = unpack 315 9 FP := eq_unpack_of_bindListK (by quickRfl)

theorem bR : j2A4RGens.size = R.ng ∧ ∀ k < R.ng, j2A4RGens[k]! = unpack 315 9 (R.G k) :=
  binds_of_listK rfl (by quickRfl)
theorem bCR : j2A4CR.size = CR.ng ∧ ∀ k < CR.ng, j2A4CR[k]! = unpack 315 9 (CR.G k) :=
  binds_of_listK rfl (by quickRfl)
theorem bL : j2A4L.size = L.ng ∧ ∀ k < L.ng, j2A4L[k]! = unpack 315 9 (L.G k) :=
  binds_of_listK rfl (by quickRfl)
theorem bC3 : j2A4C3.size = C3.ng ∧ ∀ k < C3.ng, j2A4C3[k]! = unpack 315 9 (C3.G k) :=
  binds_of_listK rfl (by quickRfl)

theorem setR : SetFacts cA4R j2A4RGens R.N R.T :=
  setOf bR.1 bR.2 (by quickRfl) R.ok (by quickRfl) (by decide)
theorem setCR : SetFacts cA4CR j2A4CR CR.N CR.T :=
  setOf bCR.1 bCR.2 (by quickRfl) CR.ok (by quickRfl) (by decide)
theorem setL : SetFacts cA4L j2A4L L.N L.T :=
  setOf bL.1 bL.2 (by quickRfl) L.ok (by quickRfl) (by decide)
theorem setC3 : SetFacts cA4C3 j2A4C3 C3.N C3.T :=
  setOf bC3.1 bC3.2 (by quickRfl) C3.ok (by quickRfl) (by decide)

theorem kCR : allN CR.ng (fun k => okK (CR.G k) && Nat.beq (cm (CR.G k) R1P) (cm R1P (CR.G k)) &&
    Nat.beq (cm (CR.G k) R2P) (cm R2P (CR.G k)) &&
    permOK 315 9 (mask 9) (315 * 9) (CR.G k) (iv (CR.G k)) &&
    canonK 315 9 (mask 9) (315 * 9) (iv (CR.G k))) = true := by quickRfl
theorem kL : allN L.ng (fun k => okK (L.G k) &&
    (List.range CR.N).any (fun i => Nat.beq (L.G k) (CR.T i)) &&
    Nat.beq (cm FP (L.G k)) (cm (L.G k) FP)) = true := by quickRfl
theorem kC3 : allN C3.ng (fun k => okK (C3.G k) && Nat.beq (cm (C3.G k) Z3P) (cm Z3P (C3.G k))) =
    true := by quickRfl

theorem crng : CR.ng = 4 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem cR1 : Can R1P := by quickRfl
theorem cR2 : Can R2P := by quickRfl
theorem cF : Can FP := by quickRfl
theorem cZ3 : Can Z3P := by quickRfl
theorem pF : PermP FP := by quickRfl
theorem cFi : Can (iv FP) := by quickRfl

theorem elts4 : j2A4Elts = true := by
  have cCR := gcan CR.hG
  have cL := gcan L.hG
  have cC3 := gcan C3.hG
  have tH := bfsK_canon H.ok
  have tR := bfsK_canon R.ok
  have tCR := bfsK_canon CR.ok
  have tL := bfsK_canon L.ok
  unfold j2A4Elts
  simp only [Bool.and_eq_true, beq_iff_eq, allLt_iff]
  and_intros
  · rw [hR1]; exact okU (by quickRfl)
  · rw [hR2]; exact okU (by quickRfl)
  · rw [hF]; exact okU (by quickRfl)
  · rw [hZ3]; exact okU (by quickRfl)
  · intro i hi
    rw [bCR.1] at hi
    have h := allN_spec kCR i hi
    simp only [Bool.and_eq_true] at h
    rw [bCR.2 i hi, hR1, hR2, commA_unpack (cCR i hi) cR1, commA_unpack (cCR i hi) cR2]
    exact ⟨⟨okU h.1.1.1.1, h.1.1.1.2⟩, h.1.1.2⟩
  · intro i hi
    rw [bL.1] at hi
    have h := allN_spec kL i hi
    simp only [Bool.and_eq_true] at h
    rw [bL.2 i hi, inCert_unpack setCR.2.1 (cL i hi) tCR]
    exact ⟨okU h.1.1, h.1.2⟩
  · intro i hi
    rw [bC3.1] at hi
    have h := allN_spec kC3 i hi
    simp only [Bool.and_eq_true] at h
    rw [bC3.2 i hi, hZ3, commA_unpack (cC3 i hi) cZ3]
    exact ⟨okU h.1, h.2⟩
  · exact setR.1
  · exact setR.2.2
  · exact setCR.1
  · exact setCR.2.2
  · exact setL.1
  · exact setL.2.2
  · exact setC3.1
  · exact setC3.2.2
  · rw [hR1, inCert_unpack setH.2.1 cR1 tH]; quickRfl
  · rw [hR2, inCert_unpack setH.2.1 cR2 tH]; quickRfl
  · intro k hk l hl
    rw [bCR.1] at hk
    rw [bL.1] at hl
    have h := allN_spec kCR k hk
    simp only [Bool.and_eq_true] at h
    rw [bCR.2 k hk, bL.2 l hl, conjA_unpack h.1.2 (cCR k hk) (cL l hl) h.2,
      inCert_unpack setL.2.1 (cj_can (cCR k hk) (cL l hl) h.2) tL]
    exact allN_spec (OCR.all k (by rw [crng] at hk; exact hk)) l hl
  · intro k hk l hl
    rw [bCR.1] at hk hl
    have h := allN_spec kCR k hk
    have h' := allN_spec kCR l hl
    simp only [Bool.and_eq_true] at h h'
    rw [bCR.2 k hk, bCR.2 l hl, commutatorA_unpack h.1.2 h'.1.2 (cCR k hk) (cCR l hl) h.2 h'.2,
      inCert_unpack setL.2.1 (cmt_can (cCR k hk) (cCR l hl) h.2 h'.2) tL]
    exact allN_spec (OCC.all k (by rw [crng] at hk; exact hk)) l hl
  · rw [hF, powArr_unpack cF 3, hid, eqU (pw_can cF 3) kPid]; quickRfl
  · rw [hF, hid, eqU cF kPid]; quickRfl
  · intro i hi
    rw [bL.1] at hi
    have h := allN_spec kL i hi
    simp only [Bool.and_eq_true] at h
    rw [bL.2 i hi, hF, commA_unpack cF (cL i hi)]
    exact h.2
  · rw [hF, hR1, conjA_unpack pF cF cR1 cFi, inCert_unpack setR.2.1 (cj_can cF cR1 cFi) tR]
    quickRfl
  · rw [hF, hR2, conjA_unpack pF cF cR2 cFi, inCert_unpack setR.2.1 (cj_can cF cR2 cFi) tR]
    quickRfl
  · rw [hF, hR1, hR2, commA_unpack cF cR1, commA_unpack cF cR2]; quickRfl
  · rw [hZ3, powArr_unpack cZ3 3, hid, eqU (pw_can cZ3 3) kPid]; quickRfl
  · rw [hZ3, hid, eqU cZ3 kPid]; quickRfl
  · rw [hZ3, inCert_unpack setL.2.1 cZ3 tL]; quickRfl
  · refine allLt_iff.1 (allLt_pts
      (f := fun x => !(eqA 315 (powArr 315 x 5) (idA 315)) || eqA 315 x (idA 315))
      setC3.2.1 fun i hi => ?_)
    have hc := bfsK_canon C3.ok i hi
    rw [powArr_unpack hc 5, hid, eqU (pw_can hc 5) kPid, eqU hc kPid]
    have hs : i / 6 < 6 := by
      have : C3.N = 36 := rfl
      omega
    have h := allN_spec (OC3.all (i / 6) hs) (i % 6) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (Nat.mul 6 (i / 6)) (i % 6) = i := Nat.div_add_mod i 6
    rwa [e] at h

theorem orb4 : j2A4Orb = true := by
  unfold j2A4Orb
  rw [orbR, orbZ3]
  rfl

theorem j2A4Check_eq_true : j2A4Check = true := by
  unfold j2A4Check
  rw [elts4, orb4]
  rfl

end CertificateChecks.KernelLC.J2Std

end
