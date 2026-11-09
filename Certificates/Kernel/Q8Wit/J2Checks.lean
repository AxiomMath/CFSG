module

public import Certificates.Kernel.Q8Wit.J2Data
public import Certificates.Data.Kernel.Q8Wit
public import Certificates.Data.Kernel.PGrp
public import Certificates.Data.Kernel.BfsPinBase
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackFld
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelQ8W.J2

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PGrp CFSG.KC.Misc.ArrEnum
open CFSG.KC.Q8Wit Certificates.TwinPerpSmSp1

@[expose] noncomputable def SK : List Nat := (List.range 256).map Q.SKT

theorem hw : szOK 315 9 = true := by quickRfl

theorem keys : keysSK 315 9 j2Wit.syl.qKeys Q.N Q.T SK = true := by quickRfl

theorem bindPG : (Nat.beq CFSG.ComponentClassification.J2Cover.sylowStrong.size 5 &&
    CFSG.KC.Enum.allN 3 fun k =>
      bindArrK CFSG.ComponentClassification.J2Cover.sylowStrong[k]! 315 9 (PG k)) = true := by
  decide +kernel

theorem bindXG : (Nat.beq j2Wit.xg.size 2 &&
    CFSG.KC.Enum.allN 2 fun k => bindArrK j2Wit.xg[k]! 315 9 (XG k)) = true := by
  decide +kernel

theorem permPG : CFSG.KC.Enum.allN 3 (fun j => permB 315 9 (PG j)) = true := by quickRfl

theorem permXG : CFSG.KC.Enum.allN 2 (fun j => permB 315 9 (XG j)) = true := by quickRfl

theorem lettersQ : (j2Wit.syl.qW.toList.all fun wd => wd.all fun l => decide (l < 3)) = true := by
  decide +kernel

theorem lettersC : (j2Wit.cW.toList.all fun wd => wd.all fun l => decide (l < 2)) = true := by
  decide +kernel

theorem wordsQ : j2Wit.syl.qW.toList.map (posWordK 315 9 PG) = (List.range Q.ng).map Q.G := by
  decide +kernel

theorem wordsC : j2Wit.cW.toList.map (posWordK 315 9 XG) = (List.range nc).map C := by
  decide +kernel

theorem tabs : tabsK 315 9 Q.N Q.T SQ I = true := by quickRfl

theorem invs : invsK 315 9 nc C CI = true := by quickRfl

theorem beq_pcomp {n w : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (a b c d : Nat) :
    Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) c d) = eq22 n w (mask w) a b c d := by
  cases h : eq22 n w (mask w) a b c d
  · cases e : Nat.beq (pcomp n w (mask w) a b) (pcomp n w (mask w) c d)
    · rfl
    · have e' := Nat.eq_of_beq_eq_true e
      have ht : eq22 n w (mask w) a b c d = true :=
        CFSG.KS.PackFld.allN_of_forall fun i hi => by
          show Nat.beq (pg w (mask w) a (pg w (mask w) b i)) (pg w (mask w) c (pg w (mask w) d i)) =
            true
          rw [← CFSG.KS.PF.pg_pcomp hn hi, ← CFSG.KS.PF.pg_pcomp hn hi, e']
          exact Nat.beq_refl _
      rw [h] at ht
      exact absurd ht (by decide)
  · have e : pcomp n w (mask w) a b = pcomp n w (mask w) c d :=
      CFSG.KS.PF.eq_of_fields hw (CFSG.KS.PF.pcomp_shr a b hn hw) (CFSG.KS.PF.pcomp_shr c d hn hw)
        fun i hi => by
          rw [CFSG.KS.PF.pg_pcomp hn hi, CFSG.KS.PF.pg_pcomp hn hi]
          exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)
    rw [e]
    exact Nat.beq_refl _

@[expose] noncomputable def commF (n w a b : Nat) : Bool := eq22 n w (mask w) a b b a

@[expose] noncomputable def outsideF (n w x y s c a : Nat) : Bool :=
  CFSG.KC.LQT.P.allN 8 fun j => !eq22 n w (mask w) c a (q8EltK n w x y s j) c

@[expose] noncomputable def wit4F (n w x y s c ci : Nat) : Bool :=
  commF n w c s && (outsideF n w x y s c x || outsideF n w x y s c y) &&
    (!commF n w x (pcomp n w (mask w) (pcomp n w (mask w) c x) ci) ||
      !commF n w x (pcomp n w (mask w) (pcomp n w (mask w) c y) ci) ||
      !commF n w y (pcomp n w (mask w) (pcomp n w (mask w) c x) ci) ||
      !commF n w y (pcomp n w (mask w) (pcomp n w (mask w) c y) ci))

@[expose] noncomputable def wit5F (n w x y s g gi : Nat) : Bool :=
  CFSG.KC.LQT.P.anyN 8 fun j =>
    (!commF n w (q8EltK n w x y s j) x || !commF n w (q8EltK n w x y s j) y) &&
      commF n w (pcomp n w (mask w) (pcomp n w (mask w) g (q8EltK n w x y s j)) gi) s &&
      (outsideF n w x y s (pcomp n w (mask w) (pcomp n w (mask w) g (q8EltK n w x y s j)) gi) x ||
        outsideF n w x y s (pcomp n w (mask w) (pcomp n w (mask w) g (q8EltK n w x y s j)) gi) y)

@[expose] noncomputable def q8WitFreeF (n w N : Nat) (T SQ I : Nat → Nat) (nc : Nat)
    (C CI : Nat → Nat) : Bool :=
  CFSG.KC.LQT.P.allN N fun i =>
    Nat.beq (SQ i) (pidn n w) || !Nat.beq (pcomp n w (mask w) (SQ i) (SQ i)) (pidn n w) ||
      CFSG.KC.LQT.P.allN N fun j =>
        !Nat.beq (SQ j) (SQ i) ||
          !eq22 n w (mask w) (T j) (T i) (I i) (T j) ||
          CFSG.KC.LQT.P.anyN nc fun k => wit4F n w (T i) (T j) (SQ i) (C k) (CI k) ||
            wit5F n w (T i) (T j) (SQ i) (C k) (CI k)

theorem q8WitFree_eqF {n w : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) (N : Nat) (T SQ I : Nat → Nat)
    (nc : Nat) (C CI : Nat → Nat) :
    q8WitFreeK n w N T SQ I nc C CI = q8WitFreeF n w N T SQ I nc C CI := by
  have hc : ∀ a b, commK n w a b = commF n w a b := fun a b => beq_pcomp hn hw a b b a
  have ho : ∀ x y s c a, outsideK n w x y s c a = outsideF n w x y s c a := fun x y s c a => by
    unfold outsideK outsideF
    simp only [beq_pcomp hn hw]
  have h4 : ∀ x y s c ci, wit4K n w x y s c ci = wit4F n w x y s c ci := fun x y s c ci => by
    unfold wit4K wit4F
    simp only [hc, ho]
  have h5 : ∀ x y s g gi, wit5K n w x y s g gi = wit5F n w x y s g gi := fun x y s g gi => by
    unfold wit5K wit5F
    simp only [hc, ho]
  unfold q8WitFreeK q8WitFreeF
  simp only [h4, h5, beq_pcomp hn hw]

theorem freeF : q8WitFreeF 315 9 Q.N Q.T SQ I nc C CI = true := by quickRfl

theorem free : q8WitFreeK 315 9 Q.N Q.T SQ I nc C CI = true := by
  rw [q8WitFree_eqF (by norm_num) (by norm_num)]
  exact freeF

end CertificateChecks.KernelQ8W.J2

end
