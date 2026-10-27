module

public import Certificates.Kernel.Misc.Perm.J2Rel
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2En

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2Fam
open CertificateChecks.KernelMisc.J2C3 (cm)
open CFSG.Monster.B.Co2 (allLt_iff)

theorem rGA {k : ℕ} (hk : k < 2) : R gensCaArr[k]! (GA k) := ⟨hga k hk, pGA k hk⟩
theorem rGV {k : ℕ} (hk : k < 2) : R gensCvArr[k]! (GV k) := ⟨hgv k hk, pGV k hk⟩
theorem rNE {k : ℕ} (hk : k < 2) : R neGens[k]! (NE k) := ⟨hne k hk, pNE k hk⟩
theorem rH1 : R h1Arr H1 := ⟨hh1, pH1⟩
theorem rHV : R hVArr HV := ⟨hhV, pHV⟩

theorem _root_.CertificateChecks.KernelMisc.J2Fam.R.commt {a b : Array ℕ} {p q : ℕ} (ha : R a p)
    (hb : R b q) : R (commutatorA 315 a b) (cm (cm p q) (cm (iv p) (iv q))) :=
  (ha.comp hb).comp (ha.inv.comp hb.inv)

theorem chkElts45_true : chkElts45 = true := by
  unfold chkElts45
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨?_, okh1, ?_, okv1, okv2, ?_, ?_, okhV, ?_, ?_, okp0, vou, ?_, ?_, ?_, ?_, ?_⟩
  · rw [allLt_iff, ga_size]
    intro k hk
    rw [okga k hk, (rGA hk).commA rX]
    interval_cases k <;> quickRfl
  · rw [(rH1.conj rX).eq (rX.comp rX)]
    quickRfl
  · rw [allLt_iff, gv_size]
    exact okgv
  · rw [allLt_iff, gv_size]
    intro k hk
    rw [(rGV hk).commA rV1, (rGV hk).commA rV2]
    interval_cases k <;> quickRfl
  · rw [(rHV.conj rV1).eq rV2]
    quickRfl
  · rw [(rHV.conj rV2).eq (rV1.comp rV2)]
    quickRfl
  · rw [allLt_iff, cc_size]
    exact okcc
  · rw [allLt_iff, wg_size]
    exact okwg
  · rw [allLt_iff, u4_size]
    exact oku4
  · rw [allLt_iff, ne_size]
    intro k hk
    rw [okne k hk, ((rNE hk).conj rZ).memE0, ((rNE hk).conj rX).memE0]
    interval_cases k <;> quickRfl
  · have rc := (rNE (k := 0) (by norm_num)).commt (rNE (k := 1) (by norm_num))
    rw [rc.commA rZ, rc.commA rX]
    quickRfl

theorem neg_h1 : (!Nat.beq (cm H1 J2C3.X) (cm J2C3.X H1)) = true := by quickRfl

theorem neg_hV : (!Nat.beq (cm HV (cm V1 (iv HV))) V1) = true := by quickRfl

end CertificateChecks.KernelMisc.J2En

end
