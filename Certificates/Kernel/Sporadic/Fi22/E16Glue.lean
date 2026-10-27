module

public import CFSG.LocalAnalysis.EvenSporadicStandard.YS14.Fi22E16Inputs
import Certificates.Kernel.Sporadic.Fi22.E16Chk
import Certificates.Kernel.Sporadic.Fi22.E2067
import Certificates.Kernel.Sporadic.Fi22.C2068
import CFSG.Certificates.Kernel.Spor.TextSound
import CFSG.Certificates.Kernel.SporSch.DerivsSound
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.BfsPinUnpack
import CFSG.Monster.B.Co2.PermArr
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22E16

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.YS14
open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Fischer

theorem arr_eq {L : Nat} (hL : L < 24) : fi22E16Arr L = unpack 3510 12 (E L) := by
  have h := hexBind_sound Fi22E16T.all L hL
  rw [Nat.zero_add, ← Fi22E16T.eq] at h
  exact h

theorem cn_E {L : Nat} (hL : L < 24) : Fi22X.cn (E L) = true := allN_spec e16cnE L hL

theorem cn_X {k : Nat} (hk : k < 6) : Fi22X.cn (Fi22ExtT.L (21 + k)) = true :=
  allN_spec e16cnX k hk

theorem cn_id : Fi22X.cn (pidn 3510 12) = true := e16cnI

theorem bit_eq : ∀ m < 16, ∀ i < 4, bit m i = m.testBit i := by decide +kernel

noncomputable def F (k m i : Nat) : Array Nat :=
  if m.testBit i then fi22E16Arr (4 * k + i) else idA 3510

theorem fac_eq {k m i : Nat} (hk : k < 6) (hm : m < 16) (hi : i < 4) :
    F k m i = unpack 3510 12 (fac k m i) ∧ Fi22X.cn (fac k m i) = true := by
  unfold F fac
  rw [bit_eq m hm i hi]
  cases m.testBit i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨idA_eq e16sz, cn_id⟩
  | true =>
    simp only [↓reduceIte]
    have hL : Nat.add (Nat.mul 4 k) i < 24 := by
      change 4 * k + i < 24
      omega
    exact ⟨arr_eq hL, cn_E hL⟩

theorem prod_eq {k m : Nat} (hk : k < 6) (hm : m < 16) :
    fi22E16ProdA k m = unpack 3510 12 (pr k m) ∧ Fi22X.cn (pr k m) = true := by
  have e : fi22E16ProdA k m =
      compA 3510 (compA 3510 (F k m 0) (F k m 1)) (compA 3510 (F k m 2) (F k m 3)) := rfl
  obtain ⟨e0, c0⟩ := fac_eq (i := 0) hk hm (by norm_num)
  obtain ⟨e1, c1⟩ := fac_eq (i := 1) hk hm (by norm_num)
  obtain ⟨e2, c2⟩ := fac_eq (i := 2) hk hm (by norm_num)
  obtain ⟨e3, c3⟩ := fac_eq (i := 3) hk hm (by norm_num)
  rw [e, e0, e1, e2, e3, Fi22X.comp_eq c0 c1, Fi22X.comp_eq c2 c3,
    Fi22X.comp_eq (Fi22X.cn_c c0 c1) (Fi22X.cn_c c2 c3)]
  exact ⟨rfl, Fi22X.cn_c (Fi22X.cn_c c0 c1) (Fi22X.cn_c c2 c3)⟩

theorem pg_c {p q x : Nat} (hp : Fi22X.cn p = true) (hx : x < 3510) :
    pg 12 (mask 12) (Fi22X.c p q) x = pg 12 (mask 12) p (pg 12 (mask 12) q x) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hx

theorem im_eq {k m x : Nat} (hk : k < 6) (hm : m < 16) (hx : x < 3510) :
    pg 12 (mask 12) (pr k m) x = im k m x := by
  obtain ⟨-, c0⟩ := fac_eq (i := 0) hk hm (by norm_num)
  obtain ⟨-, c1⟩ := fac_eq (i := 1) hk hm (by norm_num)
  obtain ⟨-, c2⟩ := fac_eq (i := 2) hk hm (by norm_num)
  obtain ⟨-, c3⟩ := fac_eq (i := 3) hk hm (by norm_num)
  have l3 := Fi22LabA.cn_lt c3 x hx
  have l2 := Fi22LabA.cn_lt c2 _ l3
  unfold pr im
  rw [pg_c (Fi22X.cn_c c0 c1) hx, pg_c c2 hx, pg_c c0 l2]

theorem comm_of {p q : Nat} (hp : Fi22X.cn p = true) (hq : Fi22X.cn q = true)
    (h : Nat.beq (Fi22X.c p q) (Fi22X.c q p) = true) :
    eqA 3510 (compA 3510 (unpack 3510 12 p) (unpack 3510 12 q))
      (compA 3510 (unpack 3510 12 q) (unpack 3510 12 p)) = true := by
  rw [Fi22X.comp_eq hp hq, Fi22X.comp_eq hq hp]
  exact Fi22X.eqA_of (Fi22X.cn_c hp hq) (Fi22X.cn_c hq hp) h

public theorem fi22E16Check_true : fi22E16Check () = true := by
  unfold fi22E16Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · have h := CFSG.KS.SporSch.hexBind_layout Fi22E16T.all (w' := 3) (n' := 3510) rfl
    rw [← Fi22E16T.eq] at h
    exact h
  · refine allLt_iff.2 fun L hL => ?_
    exact Fi22E2067.isInv_of (arr_eq hL) (allN_spec e16perm L hL)
  · refine allLt_iff.2 fun L hL => ?_
    rw [Fi22LabA.fi22InP_eq (arr_eq hL) (cn_E hL)]
    exact S.all L hL
  · refine allLt_iff.2 fun L hL => ?_
    rw [arr_eq hL, Fi22X.comp_eq (cn_E hL) (cn_E hL), idA_eq e16sz]
    exact Fi22X.eqA_of (Fi22X.cn_c (cn_E hL) (cn_E hL)) cn_id (allN_spec e16sq L hL)
  · refine allLt_iff.2 fun L hL => ?_
    rw [arr_eq hL, Fi22E2067.ext_eq (by omega)]
    exact comm_of (cn_E hL) (cn_X (by omega)) (allN_spec e16t L hL)
  · refine allLt_iff.2 fun L hL => allLt_iff.2 fun j hj => ?_
    have hj' : 4 * (L / 4) + j < 24 := by omega
    rw [arr_eq hL, arr_eq hj']
    exact comm_of (cn_E hL) (cn_E hj') (allN_spec (allN_spec e16cm L hL) j hj)
  · refine allLt_iff.2 fun k hk => allLt_iff.2 fun m hm => allLt_iff.2 fun m' hm' => ?_
    obtain ⟨em, cm⟩ := prod_eq hk hm
    obtain ⟨em', cm'⟩ := prod_eq hk hm'
    rw [em, em', eqA_unpack cm cm']
    by_cases h : m = m'
    · subst h
      simp
    · have hne : (m == m') = false := by simpa using h
      rw [hne, Bool.false_or]
      cases hb : Nat.beq (pr k m) (pr k m')
      · rfl
      · have e := Nat.eq_of_beq_eq_true hb
        have hx : pt k < 3510 := by interval_cases k <;> decide
        have ei : im k m (pt k) = im k m' (pt k) := by
          rw [← im_eq hk hm hx, ← im_eq hk hm' hx, e]
        have hD : allN 16 (fun m => allN m (fun m' =>
            Bool.not (Nat.beq (im k m' (pt k)) (im k m (pt k))))) = true := D.all k hk
        rcases Nat.lt_or_gt_of_ne h with hlt | hlt
        · have h2 := allN_spec (allN_spec hD m' hm') m hlt
          rw [ei, Nat.beq_refl] at h2
          exact absurd h2 (by decide)
        · have h2 := allN_spec (allN_spec hD m hm) m' hlt
          rw [ei, Nat.beq_refl] at h2
          exact absurd h2 (by decide)

end CertificateChecks.KernelSpor.Fi22E16
