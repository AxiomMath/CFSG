module

public import CFSG.Certificates.Kernel.GHarrisFus.Rel
public import CFSG.Certificates.Kernel.GHarrisFus.Good
public import Certificates.Kernel.GHarrisFus.CheckMul
public import Certificates.Kernel.GHarrisFus.CheckLight
public import Certificates.Kernel.GHarrisFus.CheckTab
public import Certificates.Kernel.GHarrisFus.CheckGood
public import Certificates.Kernel.GHarrisFus.CheckRel
public import Certificates.Kernel.GHarrisFus.CheckYIZ
public import Certificates.Kernel.GHarrisFus.CheckBIZ
public import Certificates.Kernel.GHarrisFus.CheckBIIZ
public import Certificates.Kernel.GHarrisFus.CheckYIIZ

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGHarrisFus

open CFSG.ComponentClassification.GHarris.SCert CFSG.KC.GHFus CFSG.KD.GHFus

theorem glue22609_mul (a b : SE) : mulK dmT mvT a.enc b.enc = (a * b).enc :=
  mulK_enc ch22609dm ch22609mv a b

theorem glue22609_cls (s : SE) : clsK CT s.enc = SE.clsTab s := clsK_enc ch22609ct s

theorem glue22609_len : L.length ≤ 87 := by decide +kernel

theorem glue22609_lanes (v q1 q2 q3 : SE) : ∀ i < 4,
    Nat.land (Nat.shiftRight (pack v q1 q2 q3) (9 * i)) 511 = (#[v, q1, q2, q3].getD i 1).enc := by
  intro i hi
  have h := rd_pack v q1 q2 q3 (i := 9 * i) (by omega)
  rw [Nat.mul_div_cancel_left i (by decide)] at h
  exact h

theorem glue22609_fus_of {A : Fus.Data} {D : FusT} {good : Nat → Bool}
    (ht : A.tableOk (· * ·) = true) (hr : relB A D = true)
    (hgood : ∀ q1 q2 q3 : SE, good (pack A.target q1 q2 q3) = true →
      A.good (· * ·) #[A.target, q1, q2, q3] = true)
    (hc : fusRange dmT mvT CT L D good 0 87 = true) : Fus.checkList [A] = true :=
  Good.checkList_of (checkM_of ht (fusRange_sound ch22609dm ch22609mv ch22609ct ch22609rows
    ch22609invs glue22609_len ht (relB_spec hr) hgood hc))

theorem glue22609_none {A : Fus.Data} : ∀ q1 q2 q3 : SE, goodNoneK (pack A.target q1 q2 q3) = true →
    A.good (· * ·) #[A.target, q1, q2, q3] = true :=
  fun _ _ _ h => absurd h Bool.false_ne_true

theorem glue22609_fixZ {A : Fus.Data}
    (hA : ∀ q, A.good (· * ·) q = (Fus.evalW (· * ·) q [1, 2, 1, 2] == SE.gen 0)) :
    ∀ q1 q2 q3 : SE, goodFixZK dmT mvT (pack A.target q1 q2 q3) = true →
      A.good (· * ·) #[A.target, q1, q2, q3] = true :=
  fun q1 q2 q3 h => (hA _).trans (Good.goodFixZ_of glue22609_mul (glue22609_lanes _ q1 q2 q3) h)

theorem glue22609_yIZ_all : fusRange dmT mvT CT L yIZ goodNoneK 0 87 = true :=
  fusRange_append (fusRange_append (fusRange_append (fusRange_append (fusRange_append
    (fusRange_append (fusRange_append ch22609yIZ_r0 ch22609yIZ_r1) ch22609yIZ_r2) ch22609yIZ_r3)
    ch22609yIZ_r4) ch22609yIZ_r5) ch22609yIZ_r6) ch22609yIZ_r7

theorem glue22609_bIZ_all : fusRange dmT mvT CT L bIZ (goodClsTK dmT mvT CT) 0 87 = true :=
  fusRange_append (fusRange_append (fusRange_append (fusRange_append (fusRange_append
    (fusRange_append (fusRange_append ch22609bIZ_r0 ch22609bIZ_r1) ch22609bIZ_r2) ch22609bIZ_r3)
    ch22609bIZ_r4) ch22609bIZ_r5) ch22609bIZ_r6) ch22609bIZ_r7

theorem glue22609_bIIZ_all : fusRange dmT mvT CT L bIIZ goodNoneK 0 87 = true :=
  fusRange_append (fusRange_append (fusRange_append (fusRange_append (fusRange_append
    (fusRange_append (fusRange_append ch22609bIIZ_r0 ch22609bIIZ_r1) ch22609bIIZ_r2)
    ch22609bIIZ_r3) ch22609bIIZ_r4) ch22609bIIZ_r5) ch22609bIIZ_r6) ch22609bIIZ_r7

theorem glue22609_yIIZ_all : fusRange dmT mvT CT L yIIZ goodNoneK 0 87 = true :=
  fusRange_append (fusRange_append (fusRange_append (fusRange_append (fusRange_append
    (fusRange_append (fusRange_append ch22609yIIZ_r0 ch22609yIIZ_r1) ch22609yIIZ_r2)
    ch22609yIIZ_r3) ch22609yIIZ_r4) ch22609yIIZ_r5) ch22609yIIZ_r6) ch22609yIIZ_r7

theorem glue22608_clsOk : SE.clsOk = true := clsOk_of ch22608clsW ch22608clsCover

theorem glue22608_goodAZ : ∀ q1 q2 q3 : SE,
    goodAZK dmT mvT CT aZ.2.2.2.1 aZx aZwit (pack Fus.aZ.target q1 q2 q3) = true →
      Fus.aZ.good (· * ·) #[Fus.aZ.target, q1, q2, q3] = true := by
  intro q1 q2 q3 h
  have hw : ∀ k < 32, ∀ i ∈ Fus.aZBase.words.getD k [], i < 4 :=
    (Fus.Data.tableFacts ch22608tab_aZ).words_lt
  rw [← Prod.mk.eta (p := aZx), ← Prod.mk.eta (p := aZx.2)] at h
  have e : Fus.aZ.good = Fus.goodAZ := by
    unfold Fus.aZ
    rfl
  rw [e]
  exact Good.goodAZ_of glue22609_mul glue22609_cls (glue22609_lanes _ q1 q2 q3) ch22608ikAZ hw
    ch22608xAZ ch22608witAZ h

theorem glue22608_aZ : Fus.checkList [Fus.aZ] = true :=
  glue22609_fus_of ch22608tab_aZ ch22608rel_aZ glue22608_goodAZ
    (fusRange_append ch22608aZ0 ch22608aZ1)

theorem glue22608_aT : Fus.checkList [Fus.aT] = true :=
  glue22609_fus_of ch22608tab_aT ch22608rel_aT glue22609_none ch22608aT

theorem glue22608_aA1L : Fus.checkList [Fus.aA1L] = true :=
  glue22609_fus_of ch22608tab_aA1L ch22608rel_aA1L glue22609_none ch22608aA1L

theorem glue22608_goodA34 : ∀ q1 q2 q3 : SE,
    goodA34K dmT mvT CT aA34.2.2.2.1 aA34x aA34wit (pack Fus.aA34.target q1 q2 q3) = true →
      Fus.aA34.good (· * ·) #[Fus.aA34.target, q1, q2, q3] = true := by
  intro q1 q2 q3 h
  have hw : ∀ k < 32, ∀ i ∈ Fus.aA34Base.words.getD k [], i < 4 :=
    (Fus.Data.tableFacts ch22608tab_aA34).words_lt
  rw [← Prod.mk.eta (p := aA34x), ← Prod.mk.eta (p := aA34x.2),
    ← Prod.mk.eta (p := aA34x.2.2)] at h
  have e : Fus.aA34.good = Fus.goodA34 := by
    unfold Fus.aA34
    rfl
  rw [e]
  exact Good.goodA34_of glue22609_mul glue22609_cls (glue22609_lanes _ q1 q2 q3) ch22608ikA34 hw
    ch22608xA34 ch22608witA34 ch22608a1 h

theorem glue22608_aA34 : Fus.checkList [Fus.aA34] = true :=
  glue22609_fus_of ch22608tab_aA34 ch22608rel_aA34 glue22608_goodA34 ch22608aA34

theorem glue22609_yIZ : Fus.checkList [Fus.yIZ] = true :=
  glue22609_fus_of ch22609tab_yIZ ch22609rel_yIZ glue22609_none glue22609_yIZ_all

theorem glue22609_yIX : Fus.checkList [Fus.yIX] = true :=
  glue22609_fus_of ch22609tab_yIX ch22609rel_yIX (glue22609_fixZ fun _ => rfl) ch22609yIX

theorem glue22609_bIZ : Fus.checkList [Fus.bIZ] = true :=
  glue22609_fus_of ch22609tab_bIZ ch22609rel_bIZ
    (fun q1 q2 q3 h => Good.goodClsT_of glue22609_mul glue22609_cls (glue22609_lanes _ q1 q2 q3) h)
    glue22609_bIZ_all

theorem glue22609_bIA1L : Fus.checkList [Fus.bIA1L] = true :=
  glue22609_fus_of ch22609tab_bIA1L ch22609rel_bIA1L glue22609_none ch22609bIA1L

theorem glue22609_bIX : Fus.checkList [Fus.bIX] = true :=
  glue22609_fus_of ch22609tab_bIX ch22609rel_bIX glue22609_none ch22609bIX

theorem glue22609_bIIZ : Fus.checkList [Fus.bIIZ] = true :=
  glue22609_fus_of ch22609tab_bIIZ ch22609rel_bIIZ glue22609_none glue22609_bIIZ_all

theorem glue22609_bIIA1L : Fus.checkList [Fus.bIIA1L] = true :=
  glue22609_fus_of ch22609tab_bIIA1L ch22609rel_bIIA1L glue22609_none ch22609bIIA1L

theorem glue22609_bIIX : Fus.checkList [Fus.bIIX] = true :=
  glue22609_fus_of ch22609tab_bIIX ch22609rel_bIIX glue22609_none ch22609bIIX

theorem glue22609_bIIA34 : Fus.checkList [Fus.bIIA34] = true :=
  glue22609_fus_of ch22609tab_bIIA34 ch22609rel_bIIA34 (glue22609_fixZ fun _ => rfl) ch22609bIIA34

theorem glue22609_yIIZ : Fus.checkList [Fus.yIIZ] = true :=
  glue22609_fus_of ch22609tab_yIIZ ch22609rel_yIIZ glue22609_none glue22609_yIIZ_all

theorem glue22609_yIIA34 : Fus.checkList [Fus.yIIA34] = true :=
  glue22609_fus_of ch22609tab_yIIA34 ch22609rel_yIIA34 glue22609_none ch22609yIIA34

theorem glue22609_yIIX : Fus.checkList [Fus.yIIX] = true :=
  glue22609_fus_of ch22609tab_yIIX ch22609rel_yIIX (glue22609_fixZ fun _ => rfl) ch22609yIIX

end CertificateChecks.KernelGHarrisFus
