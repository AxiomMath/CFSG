module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreData
public import Certificates.Kernel.Sporadic.Fi22.CentChecks
public import Certificates.Kernel.Sporadic.Fi22.CentStar
public import Certificates.Kernel.Sporadic.Fi22.FiveK
public import Certificates.Kernel.Sporadic.Fi22.C2064
public import CFSG.Sporadic.FischerOddCore.ClosureSearchEq
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Cent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.ClosBfs
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22CentE
open CertificateChecks.KernelSpor.Fi22CentK CertificateChecks.KernelSpor.Fi22CentS

noncomputable def EE : Array (Array Nat) := Array.ofFn (n := 600) fun i => unpack 3510 12 (EK i.val)

noncomputable def PE : Array Nat := unpack 600 10 (TB 0)
noncomputable def LE : Array Nat := unpack 600 10 (TB 1)
noncomputable def NE : Array Nat := unpack 1800 10 (TB 2)

theorem EE_size : EE.size = 600 := Array.size_ofFn

theorem EE_get {i : Nat} (hi : i < 600) : EE[i]! = unpack 3510 12 (EK i) := by
  rw [EE, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem rows : ∀ i < 600, rowC i = true := by
  intro i hi
  have hj : i / 10 < 60 := by omega
  have hc : chunkC (i / 10) = true := by
    generalize i / 10 = j at hj
    interval_cases j
    exacts [chunkC0, chunkC1, chunkC2, chunkC3, chunkC4, chunkC5, chunkC6, chunkC7, chunkC8,
      chunkC9, chunkC10, chunkC11, chunkC12, chunkC13, chunkC14, chunkC15, chunkC16, chunkC17,
      chunkC18, chunkC19, chunkC20, chunkC21, chunkC22, chunkC23, chunkC24, chunkC25, chunkC26,
      chunkC27, chunkC28, chunkC29, chunkC30, chunkC31, chunkC32, chunkC33, chunkC34, chunkC35,
      chunkC36, chunkC37, chunkC38, chunkC39, chunkC40, chunkC41, chunkC42, chunkC43, chunkC44,
      chunkC45, chunkC46, chunkC47, chunkC48, chunkC49, chunkC50, chunkC51, chunkC52, chunkC53,
      chunkC54, chunkC55, chunkC56, chunkC57, chunkC58, chunkC59]
  have h := Fi22CtiA.allN_iff.1 hc (i % 10) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 10 (i / 10)) (i % 10) = i := by
    change 10 * (i / 10) + i % 10 = i
    omega
  rwa [e] at h

theorem row_parts {i : Nat} (hi : i < 600) :
    Fi22X.cn (EK i) = true ∧
    (i ≠ 0 → PA i < i ∧ LA i < 3 ∧ EK i = Fi22X.c (EK (1 + LA i)) (EK (PA i))) ∧
    ∀ k < 3, NX (i * 3 + k) < 600 ∧ EK (NX (i * 3 + k)) = Fi22X.c (EK (1 + k)) (EK i) := by
  have h := rows i hi
  unfold rowC at h
  rw [Fi22CtiA.strictB_eq'] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := by simpa only [bAnd_iff] using h
  have nx : ∀ k, nxK i k (EK i) = true →
      NX (i * 3 + k) < 600 ∧ EK (NX (i * 3 + k)) = Fi22X.c (EK (1 + k)) (EK i) := by
    intro k hk
    unfold nxK at hk
    rw [Fi22CtiA.strictB_eq'] at hk
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 hk
    have e : Nat.add (Nat.mul i 3) k = i * 3 + k := rfl
    have e1 : Nat.add 1 k = 1 + k := rfl
    rw [e] at a b
    rw [e1] at b
    exact ⟨Nat.blt_eq.mp a, Nat.eq_of_beq_eq_true b⟩
  refine ⟨h1, fun h0 => ?_, fun k hk => ?_⟩
  · have hb : Nat.beq i 0 = false := by
      cases e : Nat.beq i 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true e) h0
    rw [hb] at h2
    obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using h2
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.eq_of_beq_eq_true c⟩
  · interval_cases k
    exacts [nx 0 h3, nx 1 h4, nx 2 h5]

theorem cnE {i : Nat} (hi : i < 600) : Fi22X.cn (EK i) = true := (row_parts hi).1

theorem gens_parts : EK 0 = pidn 3510 12 ∧ EK 1 = Fi22W.W (signedWord wx) ∧
    EK 2 = Fi22W.W (signedWord wy) ∧ EK 3 = Fi22W.W hw := by
  exact ⟨Nat.eq_of_beq_eq_true gen0, Nat.eq_of_beq_eq_true gen1, Nat.eq_of_beq_eq_true gen2,
    Nat.eq_of_beq_eq_true gen3⟩

theorem gens3_size : gens3.size = 3 := rfl

theorem gens3_get {k : Nat} (hk : k < 3) : gens3[k]! = unpack 3510 12 (EK (1 + k)) := by
  obtain ⟨-, e1, e2, e3⟩ := gens_parts
  interval_cases k
  · change xA = _
    rw [Fi22FiveK.x_eq, e1]
  · change yA = _
    rw [Fi22FiveK.y_eq, e2]
  · change hA = _
    rw [Fi22FiveK.h_eq, e3]

theorem eqA_E {p q : Nat} (hp : Fi22X.cn p = true) (hq : Fi22X.cn q = true) (h : p = q) :
    eqA 3510 (unpack 3510 12 p) (unpack 3510 12 q) = true := by
  rw [eqA_unpack hp hq, h]
  exact Nat.beq_refl q

theorem closure_ok : closureOK 3510 gens3 EE PE LE NE = true := by
  unfold closureOK
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [gens3_size, EE_size]
  refine ⟨⟨⟨by norm_num, ?_⟩, CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => ?_⟩,
    CFSG.Monster.B.Co2.allLt_iff.2 fun i hi => CFSG.Monster.B.Co2.allLt_iff.2 fun k hk => ?_⟩
  · rw [EE_get (by norm_num), Fi22FiveK.hI]
    exact eqA_E (cnE (by norm_num)) Fi22W.cnId gens_parts.1
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h0 : i = 0
    · exact Or.inl h0
    right
    obtain ⟨hp, hl, he⟩ := (row_parts hi).2.1 h0
    have ep : PE[i]! = PA i := Fi22CtiA.unpack_get' hi
    have el : LE[i]! = LA i := Fi22CtiA.unpack_get' hi
    rw [ep, el]
    refine ⟨⟨hp, hl⟩, ?_⟩
    rw [EE_get hi, EE_get (by omega), gens3_get hl,
      Fi22X.comp_eq (cnE (by omega)) (cnE (by omega))]
    exact eqA_E (cnE hi) (Fi22X.cn_c (cnE (by omega)) (cnE (by omega))) he
  · have en : NE[i * 3 + k]! = NX (i * 3 + k) := Fi22CtiA.unpack_get' (by omega)
    obtain ⟨hn, he⟩ := (row_parts hi).2.2 k hk
    rw [en]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hn, ?_⟩
    rw [EE_get hn, EE_get hi, gens3_get hk, Fi22X.comp_eq (cnE (by omega)) (cnE hi)]
    exact eqA_E (cnE hn) (Fi22X.cn_c (cnE (by omega)) (cnE hi)) he

theorem key_eq {i : Nat} (hi : i < 600) : keyAt 3510 fivePts EE[i]! = KY i := by
  rw [EE_get hi]
  simp only [keyAt, fivePts, List.foldr_cons, List.foldr_nil, Fi22W.get_eq_of_cn (cnE hi)]
  rfl

theorem EE_inj : ∀ i < EE.size, ∀ j < EE.size, EE[i]! = EE[j]! → i = j := by
  rw [EE_size]
  have hk := Fi22CtiA.allN_iff.1 keys
  have hinj := Fi22CtiA.inj_of_sorted (N := 600) (f := KY) (σ := SG)
    (fun m hm => by
      have h := hk m hm
      unfold keyRow at h
      exact Nat.blt_eq.mp ((bAnd_iff _ _).1 h).1)
    (fun m hm => by
      have h := hk m (by omega)
      unfold keyRow at h
      have h2 := ((bAnd_iff _ _).1 h).2
      have hb : Nat.blt m 599 = true := Nat.blt_eq.mpr (by omega)
      rw [hb] at h2
      exact Nat.blt_eq.mp h2)
  intro i hi j hj e
  apply hinj i hi j hj
  rw [← key_eq hi, ← key_eq hj, e]

theorem cent_eq : centClosure = (EE, PE, LE, NE) := by
  refine SearchSpec.closureSearch_eq_of (fn := NX) (fp := PA) (fl := LA) closure_ok
    (fun i hi => by rw [EE_get (by rw [EE_size] at hi; exact hi)]; exact Fi22CtiA.unpack_size)
    EE_inj (by rw [EE_size]; norm_num) (by rw [EE_size]; exact Fi22CtiA.unpack_size)
    (by rw [EE_size]; exact Fi22CtiA.unpack_size)
    (by rw [EE_size, gens3_size]; exact Fi22CtiA.unpack_size)
    (fun i hi => Fi22CtiA.unpack_get' (by rw [EE_size] at hi; exact hi))
    (fun i hi => Fi22CtiA.unpack_get' (by rw [EE_size] at hi; exact hi))
    (fun t ht => Fi22CtiA.unpack_get' (by rw [EE_size, gens3_size] at ht; exact ht)) ?_
  rw [gens3_size, EE_size]
  exact bfs

theorem p24_eq {v : Nat} (hv : Fi22X.cn v = true) :
    p24 (unpack 3510 12 v) = unpack 3510 12 (p24K v) ∧ Fi22X.cn (p24K v) = true := by
  have c3 := Fi22X.cn_c hv (Fi22X.cn_c hv hv)
  have c6 := Fi22X.cn_c c3 c3
  have c12 := Fi22X.cn_c c6 c6
  unfold p24 p24K
  simp only [Fi22CtiA.strictN_eq']
  rw [Fi22X.comp_eq hv hv, Fi22X.comp_eq hv (Fi22X.cn_c hv hv), Fi22X.comp_eq c3 c3,
    Fi22X.comp_eq c6 c6, Fi22X.comp_eq c12 c12]
  exact ⟨rfl, Fi22X.cn_c c12 c12⟩

section Star

variable {Q : Nat → Nat} (hQ : ∀ a < 6, yPows[a]! = unpack 3510 12 (Q a) ∧ Fi22X.cn (Q a) = true)
include hQ

theorem cj_eq {v a : Nat} (hv : Fi22X.cn v = true) (ha : a ≤ 5) :
    yConjT (unpack 3510 12 v) a = unpack 3510 12 (cjK Q v a) ∧ Fi22X.cn (cjK Q v a) = true := by
  obtain ⟨q1, c1⟩ := hQ a (by omega)
  obtain ⟨q2, c2⟩ := hQ (5 - a) (by omega)
  unfold yConjT cjK
  have e : Nat.sub 5 a = 5 - a := rfl
  rw [e, q1, q2, Fi22X.comp_eq hv c2, Fi22X.comp_eq c1 (Fi22X.cn_c hv c2)]
  exact ⟨rfl, Fi22X.cn_c c1 (Fi22X.cn_c hv c2)⟩

theorem star5_eq {v : Nat} (hv : Fi22X.cn v = true) : star5OK (unpack 3510 12 v) = star5K Q v := by
  obtain ⟨a0, b0⟩ := cj_eq hQ hv (a := 0) (by norm_num)
  obtain ⟨a1, b1⟩ := cj_eq hQ hv (a := 1) (by norm_num)
  obtain ⟨a2, b2⟩ := cj_eq hQ hv (a := 2) (by norm_num)
  obtain ⟨a3, b3⟩ := cj_eq hQ hv (a := 3) (by norm_num)
  obtain ⟨a4, b4⟩ := cj_eq hQ hv (a := 4) (by norm_num)
  have hw1 : star5W1 (unpack 3510 12 v) = unpack 3510 12 (w1K Q v) := by
    unfold star5W1 w1K
    rw [a0, a1, a2, a3, Fi22X.comp_eq b2 b3, Fi22X.comp_eq b1 (Fi22X.cn_c b2 b3),
      Fi22X.comp_eq b0 (Fi22X.cn_c b1 (Fi22X.cn_c b2 b3))]
  have cw1 : Fi22X.cn (w1K Q v) = true :=
    Fi22X.cn_c b0 (Fi22X.cn_c b1 (Fi22X.cn_c b2 b3))
  have hw2 : star5W2 (unpack 3510 12 v) = unpack 3510 12 (w2K Q v) := by
    unfold star5W2 w2K
    rw [a0, a1, a4, Fi22X.comp_eq b1 b4, Fi22X.comp_eq b0 (Fi22X.cn_c b1 b4),
      Fi22X.comp_eq b0 (Fi22X.cn_c b0 (Fi22X.cn_c b1 b4))]
  have cw2 : Fi22X.cn (w2K Q v) = true := Fi22X.cn_c b0 (Fi22X.cn_c b0 (Fi22X.cn_c b1 b4))
  obtain ⟨p0, d0⟩ := p24_eq hv
  obtain ⟨p1, d1⟩ := p24_eq cw1
  obtain ⟨p2, d2⟩ := p24_eq cw2
  unfold star5OK star5K
  rw [hw1, hw2, p0, p1, p2, Fi22FiveK.hI, eqA_unpack hv Fi22W.cnId, eqA_unpack d0 Fi22W.cnId,
    eqA_unpack d1 Fi22W.cnId, eqA_unpack d2 Fi22W.cnId]
  cases Nat.beq v (pidn 3510 12) <;> cases Nat.beq (p24K v) (pidn 3510 12) <;>
    cases Nat.beq (p24K (w1K Q v)) (pidn 3510 12) <;>
    cases Nat.beq (p24K (w2K Q v)) (pidn 3510 12) <;> rfl

end Star

noncomputable def QY : Nat → Nat :=
  tab6 (pidn 3510 12) (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12)))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
      (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12))))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
      (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12)))))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
      (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
        (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12))))))

theorem QY_eq {a : Nat} (ha : a < 6) : QY a = Fi22FiveK.pwK (Fi22W.W (signedWord wy)) a := by
  interval_cases a <;> rfl

theorem hQY : ∀ a < 6, yPows[a]! = unpack 3510 12 (QY a) ∧ Fi22X.cn (QY a) = true := by
  intro a ha
  have cY : Fi22X.cn (Fi22W.W (signedWord wy)) = true := by
    rw [← gens_parts.2.2.1]
    exact cnE (by norm_num)
  obtain ⟨e, c⟩ := Fi22FiveK.pw_eq cY a
  rw [QY_eq ha]
  refine ⟨?_, c⟩
  have hy : yPows[a]! = pw yA a := by
    rw [yPows, getElem!_pos _ a (by simpa using ha)]
    simp
  rw [hy, Fi22FiveK.y_eq, e]

theorem chunks : ∀ j < 12, chunkS j = true := by
  intro j hj
  interval_cases j
  exacts [chunkS0, chunkS1, chunkS2, chunkS3, chunkS4, chunkS5, chunkS6, chunkS7, chunkS8,
    chunkS9, chunkS10, chunkS11]

theorem star_all {i : Nat} (hi : i < 600) : star5K QY (EK i) = true := by
  have hc := chunks (i / 50) (by omega)
  unfold chunkS at hc
  simp only [Fi22CtiA.strictB_eq'] at hc
  have h := Fi22CtiA.allN_iff.1 hc (i % 50) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 50 (i / 50)) (i % 50) = i := by
    change 50 * (i / 50) + i % 50 = i
    omega
  rw [e] at h
  exact h

theorem star5 : star5Check = true := by
  unfold star5Check
  rw [cent_eq]
  change allLt EE.size (fun i => star5OK EE[i]!) = true
  rw [EE_size, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [EE_get hi, star5_eq hQY (cnE hi)]
  exact star_all hi

open Certificates in
open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem c9553 : star5Check = true := star5

end CertificateChecks.KernelSpor.Fi22Cent

end
