
module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Data3
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheck
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.Monster.B.Mathieu.SylowCore
public import Certificates.Data.CFSGNative.Schreier.Enum3
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs
public import Certificates.Kernel.Misc.Perm.J2Mult5
public import CFSG.Certificates.Kernel.Misc.SetCodesSound
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check3Inputs

set_option maxRecDepth 400000

#ks_perm CertificateChecks.KernelMisc.J2C3.X 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.xArr
#ks_perm CertificateChecks.KernelMisc.J2C3.Y 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.yArr
#ks_perm CertificateChecks.KernelMisc.J2C3.Z 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.zArr
#ks_perm CertificateChecks.KernelMisc.J2C3.G0 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.g0Arr
#ks_perm CertificateChecks.KernelMisc.J2C3.H8 9 CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.h8Arr
#kmisc_packarrs CertificateChecks.KernelMisc.J2C3.GC
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.gensCzArr 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2C3.O6
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.o6Sets 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2C3.S10
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.s10Sets 9
#kmisc_packarrs CertificateChecks.KernelMisc.J2C3.AB
  CFSG.ComponentClassification.J2Cover.autStrong 9

#ks_chars CertificateChecks.KernelMisc.J2C3.P3P CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3PHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.P3P CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3PHex
  3 315 9 27
#ks_chars CertificateChecks.KernelMisc.J2C3.P3E CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3EHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.P3E CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3EHex
  3 2 12 27
#ks_chars CertificateChecks.KernelMisc.J2C3.P3R CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3RHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.P3R CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3RHex
  3 27 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.P3L CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3LHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.P3L CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cP3LHex
  3 27 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.CzP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzPHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.CzP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzPHex
  3 315 9 1080
#ks_chars CertificateChecks.KernelMisc.J2C3.CzE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzEHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.CzE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzEHex
  3 2 12 1080
#ks_chars CertificateChecks.KernelMisc.J2C3.CzR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzRHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.CzR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzRHex
  3 1080 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.CzL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzLHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.CzL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cCzLHex
  3 1080 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.NPP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPPHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NPP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPPHex
  3 315 9 216
#ks_chars CertificateChecks.KernelMisc.J2C3.NPE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPEHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NPE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPEHex
  3 3 12 216
#ks_chars CertificateChecks.KernelMisc.J2C3.NPR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPRHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NPR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPRHex
  3 216 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.NPL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPLHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.NPL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cNPLHex
  3 216 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.ZoP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoPHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.ZoP CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoPHex
  3 315 9 560
#ks_chars CertificateChecks.KernelMisc.J2C3.ZoE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoEHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.ZoE CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoEHex
  3 2 12 560
#ks_chars CertificateChecks.KernelMisc.J2C3.ZoR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoRHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.ZoR CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoRHex
  3 560 12 1
#ks_chars CertificateChecks.KernelMisc.J2C3.ZoL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoLHex
#kmisc_hexflat CertificateChecks.KernelMisc.J2C3.ZoL CFSG.RankThree.PartTwo.Sec4.Sporadic.J2.cZoLHex
  3 560 12 1

public section

namespace CertificateChecks.KernelMisc.J2C3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.HexFlat CFSG.KC.Misc.ArrEnum
open CFSG.KC.Misc.SetCodes
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Misc.Clos (allN_iff anyN_iff)
open CertificateChecks.KernelMisc.J2M5 (okA_of)

theorem hw : szOK 315 9 = true := by quickRfl

@[expose] def Bound (c : CFSG.Monster.B.Fischer.ArrCert) (N G : ℕ) (FP FE FR FL : ℕ → ℕ) : Prop :=
  c.pts.size = N ∧ (∀ i < N, c.pts[i]! = unpack 315 9 (FP i)) ∧
    (∀ i < N, (c.edges[i]!).size = G ∧ ∀ k < G, (c.edges[i]!)[k]! = pg 12 (mask 12) (FE i) k) ∧
    (∀ i < N, c.par[i]! = pg 12 (mask 12) (FR 0) i ∧ c.lab[i]! = pg 12 (mask 12) (FL 0) i)

theorem cert_facts {N G : ℕ} {PH EH RH LH : String} {csP csE csR csL : List Char}
    {FP FE FR FL : ℕ → ℕ} (hPs : PH = String.ofList csP) (hPa : hexFlat csP 3 315 9 N FP = true)
    (hEs : EH = String.ofList csE) (hEa : hexFlat csE 3 G 12 N FE = true)
    (hRs : RH = String.ofList csR) (hRa : hexFlat csR 3 N 12 1 FR = true)
    (hLs : LH = String.ofList csL) (hLa : hexFlat csL 3 N 12 1 FL = true) :
    Bound ⟨Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 315 (315 * i.val) PH,
        Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 G (G * i.val) EH,
        CFSG.Monster.B.Fischer.hexTable3 N 0 RH, CFSG.Monster.B.Fischer.hexTable3 N 0 LH⟩
      N G FP FE FR FL := by
  have hr : CFSG.Monster.B.Fischer.hexTable3 N 0 RH = unpack N 12 (FR 0) := by
    have h := hexTable3_sound hRa 0 (by norm_num)
    rwa [Nat.mul_zero, ← hRs] at h
  have hl : CFSG.Monster.B.Fischer.hexTable3 N 0 LH = unpack N 12 (FL 0) := by
    have h := hexTable3_sound hLa 0 (by norm_num)
    rwa [Nat.mul_zero, ← hLs] at h
  refine ⟨by simp, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · change
      (Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 315 (315 * i.val) PH)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hPs]
    exact hexTable3_sound hPa i hi
  · have he : (Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 G (G * i.val) EH)[i]! =
        unpack G 12 (FE i) := by
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hEs]
      exact hexTable3_sound hEa i hi
    change (Array.ofFn fun i : Fin N => CFSG.Monster.B.Fischer.hexTable3 G (G * i.val) EH)[i]!.size
      = G ∧ _
    rw [he]
    exact ⟨by simp [unpack], fun k hk => CFSG.KC.Misc.PairCount.unpack_get hk⟩
  · change (CFSG.Monster.B.Fischer.hexTable3 N 0 RH)[i]! = _ ∧
      (CFSG.Monster.B.Fischer.hexTable3 N 0 LH)[i]! = _
    rw [hr, hl]
    exact ⟨CFSG.KC.Misc.PairCount.unpack_get hi, CFSG.KC.Misc.PairCount.unpack_get hi⟩

theorem p3 : Bound cP3 27 2 P3P.F P3E.F P3R.F P3L.F := by
  unfold cP3 cP3Lit
  exact cert_facts P3P.eq P3P.all P3E.eq P3E.all P3R.eq P3R.all P3L.eq P3L.all

theorem cz : Bound cCz 1080 2 CzP.F CzE.F CzR.F CzL.F := by
  unfold cCz cCzLit
  exact cert_facts CzP.eq CzP.all CzE.eq CzE.all CzR.eq CzR.all CzL.eq CzL.all

theorem np : Bound cNP 216 3 NPP.F NPE.F NPR.F NPL.F := by
  unfold cNP cNPLit
  exact cert_facts NPP.eq NPP.all NPE.eq NPE.all NPR.eq NPR.all NPL.eq NPL.all

theorem zo : Bound cZo 560 2 ZoP.F ZoE.F ZoR.F ZoL.F := by
  unfold cZo cZoLit
  exact cert_facts ZoP.eq ZoP.all ZoE.eq ZoE.all ZoR.eq ZoR.all ZoL.eq ZoL.all

theorem perms_of {N : ℕ} {F : ℕ → ℕ}
    (h : CFSG.KC.LQT.P.allN N (fun i => permB 315 9 (F i)) = true) :
    ∀ i < N, permB 315 9 (F i) = true :=
  (allN_iff _ _).1 h

theorem p3p : ∀ i < 27, permB 315 9 (P3P.F i) = true := perms_of (by quickRfl)
theorem czp : ∀ i < 1080, permB 315 9 (CzP.F i) = true := perms_of (by quickRfl)
theorem npp : ∀ i < 216, permB 315 9 (NPP.F i) = true := perms_of (by quickRfl)

theorem hx : xArr = unpack 315 9 X := arrBind_sound (by quickRfl)
theorem hy : yArr = unpack 315 9 Y := arrBind_sound (by quickRfl)
theorem hz : zArr = unpack 315 9 Z := arrBind_sound (by quickRfl)
theorem hg0 : g0Arr = unpack 315 9 G0 := arrBind_sound (by quickRfl)
theorem hh8 : h8Arr = unpack 315 9 H8 := arrBind_sound (by quickRfl)

theorem hgc (k : ℕ) (hk : k < 2) : gensCzArr[k]! = unpack 315 9 (GC k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)

theorem hab (k : ℕ) (hk : k < 2) : autStrong[k]! = unpack 315 9 (AB k) := by
  interval_cases k <;> exact arrBind_sound (by quickRfl)

@[expose] noncomputable def I : ℕ := pidn 315 9

theorem hI : unpack 315 9 I = idA 315 := idK_sound (by quickRfl)

theorem pX : permB 315 9 X = true := by quickRfl
theorem pY : permB 315 9 Y = true := by quickRfl
theorem pZ : permB 315 9 Z = true := by quickRfl
theorem pG0 : permB 315 9 G0 = true := by quickRfl
theorem pH8 : permB 315 9 H8 = true := by quickRfl
theorem pI : permB 315 9 I = true := by quickRfl

@[expose] noncomputable def cm (p q : ℕ) : ℕ := pcomp 315 9 (mask 9) p q

theorem eqT {p q : ℕ} (hp : permB 315 9 p = true) (hq : permB 315 9 q = true)
    (h : Nat.beq p q = true) : eqA 315 (unpack 315 9 p) (unpack 315 9 q) = true := by
  rw [eqA_unpack hw hp hq]
  exact h

theorem okx : okA xArr = true := okA_of hx (by quickRfl) (by quickRfl) (by quickRfl)
theorem oky : okA yArr = true := okA_of hy (by quickRfl) (by quickRfl) (by quickRfl)
theorem okz : okA zArr = true := okA_of hz (by quickRfl) (by quickRfl) (by quickRfl)
theorem okg0 : okA g0Arr = true := okA_of hg0 (by quickRfl) (by quickRfl) (by quickRfl)
theorem okh8 : okA h8Arr = true := okA_of hh8 (by quickRfl) (by quickRfl) (by quickRfl)

theorem gcz_size : gensCzArr.size = 2 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem okgc : allLt gensCzArr.size (fun k => okA gensCzArr[k]!) = true := by
  rw [allLt_iff, gcz_size]
  intro k hk
  interval_cases k
  · exact okA_of (hgc 0 (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)
  · exact okA_of (hgc 1 (by norm_num)) (by quickRfl) (by quickRfl) (by quickRfl)

theorem x3 : eqA 315 (powArr 315 xArr 3) (idA 315) = true := by
  rw [hx, pow_unpack hw pX, ← hI]
  exact eqT (by quickRfl) pI (by quickRfl)

theorem y3 : eqA 315 (powArr 315 yArr 3) (idA 315) = true := by
  rw [hy, pow_unpack hw pY, ← hI]
  exact eqT (by quickRfl) pI (by quickRfl)

theorem zxy : eqA 315 zArr (commutatorA 315 xArr yArr) = true := by
  rw [hz, hx, hy, commutator_unpack hw pX pY]
  exact eqT pZ (by quickRfl) (by quickRfl)

theorem zx : commA zArr xArr = true := by
  unfold commA
  rw [hz, hx, comp_unpack hw pZ pX, comp_unpack hw pX pZ]
  exact eqT (by quickRfl) (by quickRfl) (by quickRfl)

theorem zy : commA zArr yArr = true := by
  unfold commA
  rw [hz, hy, comp_unpack hw pZ pY, comp_unpack hw pY pZ]
  exact eqT (by quickRfl) (by quickRfl) (by quickRfl)

theorem zne : (!eqA 315 zArr (idA 315)) = true := by
  rw [hz, ← hI, eqA_unpack hw pZ pI]
  quickRfl

theorem gcz : allLt gensCzArr.size (fun k => commA gensCzArr[k]! zArr) = true := by
  rw [allLt_iff, gcz_size]
  intro k hk
  unfold commA
  have hp : permB 315 9 (GC k) = true := by interval_cases k <;> quickRfl
  rw [hgc k hk, hz, comp_unpack hw hp pZ, comp_unpack hw pZ hp]
  exact eqT (by interval_cases k <;> quickRfl) (by interval_cases k <;> quickRfl)
    (by interval_cases k <;> quickRfl)

theorem g0z : eqA 315 (conjA 315 g0Arr zArr) (compA 315 zArr zArr) = true := by
  rw [hg0, hz, conj_unpack hw pG0 pZ, comp_unpack hw pZ pZ]
  exact eqT (by quickRfl) (by quickRfl) (by quickRfl)

theorem inP3 {c : ℕ} (hc : permB 315 9 c = true) :
    inCert cP3 (unpack 315 9 c) = memK 27 P3P.F c := by
  unfold inCert
  exact any_eqA_unpack hw p3.1 p3.2.1 p3p hc

theorem h8x : inCert cP3 (conjA 315 h8Arr xArr) = true := by
  rw [hh8, hx, conj_unpack hw pH8 pX, inP3 (by quickRfl)]
  quickRfl

theorem h8y : inCert cP3 (conjA 315 h8Arr yArr) = true := by
  rw [hh8, hy, conj_unpack hw pH8 pY, inP3 (by quickRfl)]
  quickRfl

theorem h84 : (!inCert cP3 (powArr 315 h8Arr 4)) = true := by
  rw [hh8, pow_unpack hw pH8, inP3 (by quickRfl)]
  quickRfl

theorem h88 : inCert cP3 (powArr 315 h8Arr 8) = true := by
  rw [hh8, pow_unpack hw pH8, inP3 (by quickRfl)]
  quickRfl

theorem elts : chkElts = true := by
  unfold chkElts
  rw [okx, oky, okz, okg0, okh8, okgc, x3, y3, zxy, zx, zy, zne, gcz, g0z, h8x, h8y, h84, h88]
  rfl

end CertificateChecks.KernelMisc.J2C3

end
