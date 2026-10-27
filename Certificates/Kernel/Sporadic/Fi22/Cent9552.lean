module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveData
public import Certificates.Kernel.Sporadic.Fi22.Cent9553
public import Certificates.Kernel.Sporadic.Fi22.CentStar8
public import Certificates.Kernel.Sporadic.Fi22.C2068
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22Cent8

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Guest
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Fi22CentE
open CertificateChecks.KernelSpor.Fi22CentK CertificateChecks.KernelSpor.Fi22CentS
open CertificateChecks.KernelSpor.Fi22CentT CertificateChecks.KernelSpor.Fi22Cent

theorem gens_parts : Fi22X.cn (Fi22W.W hw) = true ∧
    Fi22X.cn (Fi22X.c Fi22X.GO (Fi22W.W uw)) = true ∧ Fi22X.cn (Fi22W.W (signedWord wx)) = true ∧
    Fi22X.cn (Fi22W.W uw) = true ∧
    Nat.beq (Fi22X.c (Fi22W.W hw) (Fi22W.W (signedWord wx)))
      (Fi22X.c (Fi22W.W (signedWord wx)) (Fi22W.W hw)) = true ∧
    Nat.beq (Fi22X.c (Fi22X.c Fi22X.GO (Fi22W.W uw)) (Fi22W.W (signedWord wx)))
      (Fi22X.c (Fi22W.W (signedWord wx)) (Fi22X.c Fi22X.GO (Fi22W.W uw))) = true ∧
    Fi22X.siftP (Fi22X.c Fi22X.GO (Fi22W.W uw)) = false := by
  have h := gens
  unfold gensK at h
  rw [Fi22CtiA.strictB_eq', Fi22CtiA.strictB_eq', Fi22CtiA.strictB_eq'] at h
  obtain ⟨h, g⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, f⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, e⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, d⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h, c⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h
  exact ⟨a, b, c, d, e, f, by simpa using g⟩

theorem lw : lettersK 2 uw = true := by quickRfl

theorem gens_ok : centGensOK = true := by
  obtain ⟨cH, cU, cX, cW, kH, kU, kS⟩ := gens_parts
  have hu : uA = unpack 3510 12 (Fi22X.c Fi22X.GO (Fi22W.W uw)) := by
    rw [uA, wA, Fi22FiveK.eval_eq lw, Fi22X.go_eq, Fi22X.comp_eq Fi22X.cnG cW]
  have hl : (lettersOK 2 hw && lettersOK 2 uw) = true := by decide +kernel
  simp only [Bool.and_eq_true] at hl
  unfold centGensOK commA
  rw [Fi22FiveK.h_eq, Fi22FiveK.x_eq, hu, Fi22FiveK.comp_beq cH cX cX cH,
    Fi22FiveK.comp_beq cU cX cX cU, Fi22LabA.fi22InP_eq rfl cU, kH, kU, kS, hl.1, hl.2]
  rfl

theorem KY_inj : ∀ i < 600, ∀ j < 600, KY i = KY j → i = j := by
  have hk := Fi22CtiA.allN_iff.1 keys
  exact Fi22CtiA.inj_of_sorted (N := 600) (f := KY) (σ := SG)
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

theorem keys_ok : keysOK 3510 fivePts EE = true := by
  apply Fi22CtiA.keysOK_of_nodup
  have hl : EE.toList.map (keyAt 3510 fivePts) = List.ofFn (n := 600) fun i => KY i.val := by
    apply List.ext_getElem
    · rw [List.length_map, Array.length_toList, EE_size, List.length_ofFn]
    · intro k h1 h2
      have hk : k < 600 := by
        rw [List.length_ofFn] at h2
        exact h2
      rw [List.getElem_map, List.getElem_ofFn, Array.getElem_toList,
        ← getElem!_pos EE k (by rw [EE_size]; exact hk), key_eq hk]
  rw [hl, List.nodup_ofFn]
  intro i j e
  exact Fin.ext (KY_inj i.1 i.2 j.1 j.2 e)

theorem closure_all : centClosureOK = true := by
  unfold centClosureOK
  rw [cent_eq]
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨closure_ok, EE_size⟩, keys_ok⟩

theorem any_range_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ a < n, f a = g a) →
    (List.range n).any f = (List.range n).any g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.any_append, List.any_append,
      any_range_congr (fun a ha => h a (by omega)), List.any_cons, List.any_cons, h n (by omega),
      List.any_nil, List.any_nil]

section Star

variable {Q : Nat → Nat} (hQ : ∀ a < 6, pw yA a = unpack 3510 12 (Q a) ∧ Fi22X.cn (Q a) = true)
include hQ

theorem cj_eq {v a : Nat} (hv : Fi22X.cn v = true) (ha : a ≤ 5) :
    yConj (unpack 3510 12 v) a = unpack 3510 12 (cjK Q v a) ∧ Fi22X.cn (cjK Q v a) = true := by
  obtain ⟨q1, c1⟩ := hQ a (by omega)
  obtain ⟨q2, c2⟩ := hQ (5 - a) (by omega)
  unfold yConj cjK
  have e : Nat.sub 5 a = 5 - a := rfl
  rw [e, q1, q2, Fi22X.comp_eq hv c2, Fi22X.comp_eq c1 (Fi22X.cn_c hv c2)]
  exact ⟨rfl, Fi22X.cn_c c1 (Fi22X.cn_c hv c2)⟩

theorem st_eq {v a b : Nat} (hv : Fi22X.cn v = true) (ha : a < 5) (hb : b < 5) :
    eqA 3510 (pw (starElt (unpack 3510 12 v) a b) 8) (unpack 3510 12 (pidn 3510 12)) =
      Nat.beq (st8K Q v a b) (pidn 3510 12) := by
  obtain ⟨ea, ca⟩ := cj_eq hQ hv (a := a) (by omega)
  obtain ⟨eb, cb⟩ := cj_eq hQ hv (a := b) (by omega)
  obtain ⟨e7, c7⟩ := Fi22FiveK.pw_eq ca 7
  have cp := Fi22X.cn_c c7 cb
  obtain ⟨e8, c8⟩ := Fi22FiveK.pw_eq cp 8
  unfold starElt st8K
  rw [ea, eb, e7, Fi22X.comp_eq c7 cb, e8]
  exact eqA_unpack c8 Fi22W.cnId

theorem star_eq {v : Nat} (hv : Fi22X.cn v = true) : starOK (unpack 3510 12 v) = starK Q v := by
  obtain ⟨e8, c8⟩ := Fi22FiveK.pw_eq hv 8
  unfold starOK starK
  rw [e8, Fi22FiveK.hI, eqA_unpack hv Fi22W.cnId, eqA_unpack c8 Fi22W.cnId]
  congr 1
  refine any_range_congr fun a ha => any_range_congr fun b hb => ?_
  rw [st_eq hQ hv ha hb]

end Star

noncomputable def QY8 : Nat → Nat :=
  tab6 (pidn 3510 12) (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12)))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
      (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12))))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
      (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12)))))
    (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
      (Fi22X.c (Fi22W.W (signedWord wy)) (Fi22X.c (Fi22W.W (signedWord wy))
        (Fi22X.c (Fi22W.W (signedWord wy)) (pidn 3510 12))))))

theorem QY8_eq {a : Nat} (ha : a < 6) : QY8 a = Fi22FiveK.pwK (Fi22W.W (signedWord wy)) a := by
  interval_cases a <;> rfl

theorem hQY' : ∀ a < 6, pw yA a = unpack 3510 12 (QY8 a) ∧ Fi22X.cn (QY8 a) = true := by
  intro a ha
  have cY : Fi22X.cn (Fi22W.W (signedWord wy)) = true := by
    rw [← Fi22Cent.gens_parts.2.2.1]
    exact cnE (by norm_num)
  obtain ⟨e, c⟩ := Fi22FiveK.pw_eq cY a
  rw [QY8_eq ha, Fi22FiveK.y_eq]
  exact ⟨e, c⟩

theorem ap_lt {X p : Nat} (hX : Fi22X.cn X = true) (hp : p < 3510) : ap X p < 3510 :=
  Nat.blt_eq.mp (Fi22CtiA.allN_iff.1 (CFSG.KS.Raw.range_of_canonK (n := 3510) (w := 12) hX) p hp)

theorem ap_c {X Z p : Nat} (hp : p < 3510) : ap (Fi22X.c X Z) p = ap X (ap Z p) :=
  CFSG.KS.PF.pg_pcomp (n := 3510) (w := 12) (p := X) (q := Z) (by norm_num) hp

theorem ap_id {p : Nat} (hp : p < 3510) : ap (pidn 3510 12) p = p :=
  CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hp

theorem ap_pwK {X : Nat} (hX : Fi22X.cn X = true) :
    ∀ k, ∀ p < 3510, ap (Fi22FiveK.pwK X k) p = itP (ap X) k p ∧ itP (ap X) k p < 3510
  | 0, p, hp => ⟨ap_id hp, hp⟩
  | k + 1, p, hp => by
    obtain ⟨e, h⟩ := ap_pwK hX k p hp
    have e2 : Fi22FiveK.pwK X (k + 1) = Fi22X.c X (Fi22FiveK.pwK X k) := rfl
    have e3 : itP (ap X) (k + 1) p = ap X (itP (ap X) k p) := rfl
    rw [e2, e3, ap_c hp, e]
    exact ⟨rfl, ap_lt hX h⟩

theorem itP_congr {f g : Nat → Nat} (hfg : ∀ p < 3510, f p = g p) (hf : ∀ p < 3510, f p < 3510) :
    ∀ k, ∀ p < 3510, itP f k p = itP g k p ∧ itP f k p < 3510
  | 0, _, hp => ⟨rfl, hp⟩
  | k + 1, p, hp => by
    obtain ⟨e, h⟩ := itP_congr hfg hf k p hp
    have e1 : itP f (k + 1) p = f (itP f k p) := rfl
    have e2 : itP g (k + 1) p = g (itP g k p) := rfl
    rw [e1, e2, ← e]
    exact ⟨hfg _ h, hf _ h⟩

theorem ne_of_moves {X : Nat} {f : Nat → Nat} (hm : movesB f = true)
    (hX : ∀ p < 3510, ap X p = f p) : Nat.beq X (pidn 3510 12) = false := by
  cases hb : Nat.beq X (pidn 3510 12)
  · rfl
  · have e := Nat.eq_of_beq_eq_true hb
    have hall : allN 6 (fun t => strictB (bp t) fun p => Nat.beq (f p) p) = true := by
      refine Fi22CtiA.allN_iff.2 fun t ht => ?_
      rw [Fi22CtiA.strictB_eq']
      have hbt : bp t < 3510 := by
        interval_cases t <;> decide
      rw [← hX _ hbt, e, ap_id hbt]
      exact Nat.beq_refl _
    unfold movesB at hm
    rw [hall] at hm
    exact absurd hm (by decide)

section StarB

variable {Q : Nat → Nat} (hQ : ∀ a < 6, Fi22X.cn (Q a) = true)
include hQ

theorem cn_cjK {v a : Nat} (hv : Fi22X.cn v = true) (ha : a ≤ 5) : Fi22X.cn (cjK Q v a) = true :=
  Fi22X.cn_c (hQ a (by omega)) (Fi22X.cn_c hv (hQ (Nat.sub 5 a) (by change 5 - a < 6; omega)))

theorem ap_cjK {v a p : Nat} (hv : Fi22X.cn v = true) (ha : a ≤ 5) (hp : p < 3510) :
    ap (cjK Q v a) p = cjP Q v a p ∧ cjP Q v a p < 3510 := by
  have c1 := hQ a (by omega)
  have c2 := hQ (Nat.sub 5 a) (by change 5 - a < 6; omega)
  unfold cjK cjP
  rw [ap_c hp, ap_c hp]
  exact ⟨rfl, ap_lt c1 (ap_lt hv (ap_lt c2 hp))⟩

theorem ap_st8K {v a b : Nat} (hv : Fi22X.cn v = true) (ha : a < 5) (hb : b < 5) :
    ∀ p < 3510, ap (st8K Q v a b) p = st8P Q v a b p := by
  have ca := cn_cjK hQ hv (a := a) (by omega)
  have cb := cn_cjK hQ hv (a := b) (by omega)
  have c7 := (Fi22FiveK.pw_eq ca 7).2
  have cM := Fi22X.cn_c c7 cb
  have hM : ∀ x < 3510, ap (Fi22X.c (Fi22FiveK.pwK (cjK Q v a) 7) (cjK Q v b)) x =
      itP (cjP Q v a) 7 (cjP Q v b x) := by
    intro x hx
    obtain ⟨eb, lb⟩ := ap_cjK hQ hv (a := b) (by omega) hx
    rw [ap_c hx, eb, (ap_pwK ca 7 _ lb).1]
    exact (itP_congr (fun y hy => (ap_cjK hQ hv (a := a) (by omega) hy).1)
      (fun y hy => ap_lt ca hy) 7 _ lb).1
  intro p hp
  unfold st8K st8P
  rw [(ap_pwK cM 8 p hp).1]
  exact (itP_congr (g := fun x => itP (cjP Q v a) 7 (cjP Q v b x)) hM (fun y hy => ap_lt cM hy)
    8 p hp).1

theorem starK_of_B {v : Nat} (hv : Fi22X.cn v = true) (h : starB Q v = true) :
    starK Q v = true := by
  unfold starB at h
  unfold starK
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl h)
  · refine Or.inl (Or.inr ?_)
    rw [ne_of_moves h fun p hp => (ap_pwK hv 8 p hp).1]
    rfl
  · refine Or.inr ?_
    rw [List.any_eq_true] at h ⊢
    obtain ⟨a, ha, h⟩ := h
    try dsimp only at h
    rw [List.any_eq_true] at h
    obtain ⟨b, hb, h⟩ := h
    refine ⟨a, ha, List.any_eq_true.2 ⟨b, hb, ?_⟩⟩
    try dsimp only
    rw [ne_of_moves h (ap_st8K hQ hv (List.mem_range.1 ha) (List.mem_range.1 hb))]
    rfl

end StarB

theorem starT_all {i : Nat} (hi : i < 600) : starK QY8 (EK i) = true := by
  have hc := starAll
  unfold starAllK at hc
  simp only [Fi22CtiA.strictB_eq'] at hc
  exact starK_of_B (fun a ha => (hQY' a ha).2) (cnE hi) (Fi22CtiA.allN_iff.1 hc i hi)

theorem star_all : centStarOK = true := by
  unfold centStarOK
  rw [cent_eq]
  change allLt EE.size (fun i => starOK EE[i]!) = true
  rw [EE_size, CFSG.Monster.B.Co2.allLt_iff]
  intro i hi
  rw [EE_get hi, star_eq hQY' (cnE hi)]
  exact starT_all hi

theorem cent : centCheck = true := by
  unfold centCheck
  rw [gens_ok, closure_all, star_all]
  rfl

open Certificates in
open CFSG.AGLEmbedding.KFactProofs.Fi22Five in
theorem c9552 : centCheck = true := cent

end CertificateChecks.KernelSpor.Fi22Cent8

end
