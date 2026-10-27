
module

public import Certificates.Kernel.Misc.Perm.J2C3A
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.SetCodes
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff anyN_iff allR forall_of_chunks)
open CertificateChecks.KernelMisc.J2M5 (okA_of)

@[expose] noncomputable def EF' (FE : ℕ → ℕ) (i k : ℕ) : ℕ := pg 12 (mask 12) (FE i) k

@[expose] noncomputable def VF' (FR : ℕ → ℕ) (i : ℕ) : ℕ := pg 12 (mask 12) (FR 0) i

theorem keys_of' {N : ℕ} {F : ℕ → ℕ} (h : keysK 315 9 keyPts F 0 N = true) :
    ∀ i < N, ∀ j < i, keyK 315 9 keyPts (F i) ≠ keyK 315 9 keyPts (F j) := by
  intro i hi j hj he
  have e : Nat.add 0 i = i := Nat.zero_add i
  have h1 := (allN_iff _ _).1 h i hi
  rw [e] at h1
  have h2 := (allN_iff _ _).1 h1 j hj
  rw [he, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

@[expose] noncomputable def okK (p : ℕ) : Bool :=
  invEqK 315 9 (mask 9) (315 * 9) p (pinvS 315 9 (mask 9) p) &&
    Nat.beq (Nat.shiftRight p (315 * 9)) 0 &&
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) CertificateChecks.KernelMisc.J2M5.C.LR
      CertificateChecks.KernelMisc.J2M5.C.TRI CertificateChecks.KernelMisc.J2M5.C.BP 3 0 p

theorem okA_of_okK {p : ℕ} (h : okK p = true) : okA (unpack 315 9 p) = true := by
  simp only [okK, Bool.and_eq_true] at h
  exact okA_of rfl h.1.1 h.1.2 h.2

theorem zo_ok : CFSG.KC.LQT.P.allN 560 (fun i => okK (ZoP.F i)) = true := by quickRfl

theorem zo_points : CFSG.KC.LQT.P.allN 560 (fun i => pointA 315 9 2 560 (conjAct 315 9 AB) ZoP.F
    (EF' ZoE.F) (VF' ZoR.F) (VF' ZoL.F) i) = true := by
  quickRfl

theorem va : validA 315 autStrong[0]! = true := by
  rw [hab 0 (by norm_num)]
  exact validA_unpack (r := pinvS 315 9 (mask 9) (AB 0)) (by quickRfl)

theorem vb : validA 315 autStrong[1]! = true := by
  rw [hab 1 (by norm_num)]
  exact validA_unpack (r := pinvS 315 9 (mask 9) (AB 1)) (by quickRfl)

theorem zo_cert :
    CFSG.Monster.B.Fischer.arrCertOK zConj 2 okA (keyA 315 keyPts) zArr cZo = true := by
  rw [hz]
  exact certA_sound (R := Z) (G := AB) (PT := ZoP.F) hw (by decide) hab
    (fun k hk => by interval_cases k <;> quickRfl) zo.1 zo.2.1 zo.2.2.1
    (fun i hi => zo.2.2.2 i hi) (by norm_num) (Nat.eq_of_beq_eq_true (by quickRfl))
    (fun i hi => by rw [zo.2.1 i hi]; exact okA_of_okK ((allN_iff _ _).1 zo_ok i hi))
    ((allN_iff _ _).1 zo_points) (keys_of' (by quickRfl))

theorem cls : chkClass = true := by
  unfold chkClass
  rw [va, vb, zo_cert, zo.1]
  rfl

theorem inZ_unpack {p : ℕ} (hp : permB 315 9 p = true) :
    inZ (unpack 315 9 p) = (Nat.beq p I || Nat.beq p Z || Nat.beq p (cm Z Z)) := by
  unfold inZ
  rw [hz, ← hI, eqA_unpack hw hp pI, eqA_unpack hw hp pZ, comp_unpack hw pZ pZ,
    eqA_unpack hw hp (by quickRfl)]
  rfl

theorem kfix : CFSG.KC.LQT.P.allN 27 (fun k => (Nat.beq (P3P.F k) I || Nat.beq (P3P.F k) Z ||
    Nat.beq (P3P.F k) (cm Z Z)) || fixK 315 9 (P3P.F k) == 0) = true := by quickRfl

theorem fix : chkFix = true := by
  unfold chkFix
  have h1 : (fixedCount 315 zArr == 45) = true := by
    rw [hz, fixedCount_unpack hw]
    quickRfl
  have h2 : allLt cP3.pts.size (fun k => inZ cP3.pts[k]! || fixedCount 315 cP3.pts[k]! == 0) =
      true := by
    rw [allLt_iff, p3.1]
    intro k hk
    rw [p3.2.1 k hk, inZ_unpack (p3p k hk), fixedCount_unpack hw]
    exact (allN_iff _ _).1 kfix k hk
  rw [h1, h2]
  rfl

theorem hO6 : o6Sets.size = 6 ∧ ∀ i < 6, o6Sets[i]! = unpack 15 9 (O6 i) :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), fun i hi => by
    interval_cases i <;> exact arrBind_sound (by quickRfl)⟩

theorem hS10 : s10Sets.size = 10 ∧ ∀ i < 10, s10Sets[i]! = unpack 9 9 (S10 i) :=
  ⟨Nat.eq_of_beq_eq_true (by quickRfl), fun i hi => by
    interval_cases i <;> exact arrBind_sound (by quickRfl)⟩

theorem lt_of {m L : ℕ} {SC : ℕ → ℕ}
    (h : CFSG.KC.LQT.P.allN m (fun i => CFSG.KC.LQT.P.allN L fun q =>
      Nat.blt (pg 9 (mask 9) (SC i) q) 315) = true) :
    ∀ i < m, ∀ q < L, pg 9 (mask 9) (SC i) q < 315 := by
  intro i hi q hq
  exact Nat.blt_eq ▸ (allN_iff _ _).1 ((allN_iff _ _).1 h i hi) q hq

theorem hO6lt : ∀ i < 6, ∀ q < 15, pg 9 (mask 9) (O6 i) q < 315 := lt_of (by quickRfl)

theorem hS10lt : ∀ i < 10, ∀ q < 9, pg 9 (mask 9) (S10 i) q < 315 := lt_of (by quickRfl)

@[expose] noncomputable def sixK (p : ℕ) : Bool :=
  permutesK 6 15 9 O6 p &&
    (!fixesK 6 15 9 O6 p || (Nat.beq p I || Nat.beq p Z || Nat.beq p (cm Z Z)))

@[expose] noncomputable def sixC (c : ℕ) : Bool := allR (270 * c) 270 fun k => sixK (CzP.F k)

end CertificateChecks.KernelMisc.J2C3

#kc_each CertificateChecks.KernelMisc.J2C3.sixC 0 4

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.SetCodes
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (forall_of_chunks)

#kc_forall_chunks sixS (fun c => sixC c = true) 4 CertificateChecks.KernelMisc.J2C3.sixC 1

theorem sixAll : ∀ k < 1080, sixK (CzP.F k) = true := forall_of_chunks 270 4 _ sixS

theorem six : chkSix = true := by
  unfold chkSix
  have h1 : allLt cCz.pts.size (fun k => permutesSets o6Sets cCz.pts[k]! &&
      (!fixesSets o6Sets cCz.pts[k]! || inZ cCz.pts[k]!)) = true := by
    rw [allLt_iff, cz.1]
    intro k hk
    rw [cz.2.1 k hk, permutes_sound hO6 hO6lt, fixes_sound hO6 hO6lt, inZ_unpack (czp k hk)]
    exact sixAll k hk
  have h2 : allLt gensCzArr.size (fun k => actsBy o6Sets gensCzArr[k]! (sigCz.getD k [])) =
      true := by
    rw [allLt_iff, gcz_size]
    intro k hk
    have hσ : ∀ i < 6, (sigCz.getD k []).getD i 0 < 6 := by
      interval_cases k <;> decide
    rw [hgc k hk, acts_sound hO6 hO6lt hσ]
    interval_cases k <;> quickRfl
  rw [h1, h2]
  rfl

theorem sets : chkSets = true := by
  unfold chkSets
  have h1 : setsOK o6Sets 15 = true := by
    rw [setsOK_sound hO6]
    quickRfl
  have h2 : setsOK s10Sets 9 = true := by
    rw [setsOK_sound hS10]
    quickRfl
  have h3 : fixesSets o6Sets zArr = true := by
    rw [hz, fixes_sound hO6 hO6lt]
    quickRfl
  have h4 : fixesSets s10Sets zArr = true := by
    rw [hz, fixes_sound hS10 hS10lt]
    quickRfl
  rw [hO6.1, hS10.1, h1, h2, h3, h4]
  rfl

end CertificateChecks.KernelMisc.J2C3

end
