module

public import Certificates.Kernel.Sporadic.ONPl.C501
public import Certificates.Kernel.Sporadic.ONPv.Facts
public import CFSG.Certificates.Kernel.Spor.ONPlSound
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.PlaneFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.ONPair.LineStab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONPl

open CFSG.KC.Enum CFSG.KS CFSG.KS.ONNQ CFSG.KS.ONPv CFSG.KS.ONPl CFSG.ONSchreier CFSG.LocalAnalysis.RankThreeTheoremC.ONPair
open CFSG.RankThree.Native CertificateChecks.KernelSpor.ONPv
open scoped commutatorElement

@[expose] def rW (e f : Nat) : List Int :=
  (List.replicate e [1, 3, -1, -3]).flatten ++ List.replicate f 3

theorem wv_rW {n : Nat} (g : Nat → Equiv.Perm (Fin n)) (e f : Nat) :
    wv g (rW e f) = (g 0 * g 2 * (g 0)⁻¹ * (g 2)⁻¹) ^ e * g 2 ^ f := by
  have h1 : ∀ e, wv g (List.replicate e [1, 3, -1, -3]).flatten =
      (g 0 * g 2 * (g 0)⁻¹ * (g 2)⁻¹) ^ e := by
    intro e
    induction e with
    | zero => simp [wv]
    | succ e ih =>
      rw [List.replicate_succ, List.flatten_cons, wv_append, ih, pow_succ']
      simp [wv, lv, mul_assoc]
  have h2 : ∀ f, wv g (List.replicate f 3) = g 2 ^ f := by
    intro f
    induction f with
    | zero => simp [wv]
    | succ f ih =>
      rw [List.replicate_succ, wv_cons, ih, pow_succ']
      simp [lv]
  rw [rW, wv_append, h1, h2]

theorem itemsE_ok : ItemsE OPL.D := by decide +kernel

theorem items_pl : (∀ j < 28, wd (OPL.D j) = planeU[j]!) ∧
    (∀ j < 28, wd (OPL.D (28 + j)) = planeM[j]!) ∧ (∀ k < 15, wd (OPL.D (56 + k)) = xHWords[k]!) ∧
    (∀ j < 28, wd (OPL.D (71 + 2 * j)) = rW planeE[j]!.1 planeE[j]!.2.1 ∧
      wd (OPL.D (72 + 2 * j)) = rW planeE[j]!.2.2.1 planeE[j]!.2.2.2) := by
  decide +kernel

theorem items_pairs : wd (OPL.D 127) = rW 7 0 ∧ wd (OPL.D 128) = [] ∧ wd (OPL.D 129) = rW 0 7 ∧
    wd (OPL.D 130) = [] ∧ wd (OPL.D 131) = rW 1 1 ∧ wd (OPL.D 132) = [3, 1, 3, -1, -3] ∧
    wd (OPL.D 133) = [1, 1, 3, -1, -3, -1] ∧ wd (OPL.D 134) = rW 1 0 ∧
    wd (OPL.D 135) = [1, 3, -1] ∧ wd (OPL.D 136) = rW 1 1 ∧
    wd (OPL.D 137) = [2, 1, 3, -1, -3, -2] ∧ wd (OPL.D 138) = rW 1 1 ∧
    wd (OPL.D 139) = [2, 3, -2] ∧ wd (OPL.D 140) = rW 0 1 := by
  decide +kernel

theorem hA2 : ∀ k < 2, Lm 2 (wd (OPV.D (77 + k))) := by decide +kernel

section Facts


theorem P3' {f : Nat → Bool} (h0 : f 0 = true) (h1 : f 227759 = true) (h2 : f 100817 = true) :
    ∀ p ∈ [(⟨0, by decide⟩ : Fin 245520), ⟨227759, by decide⟩, ⟨100817, by decide⟩],
      f p = true :=
  P3 (f := fun p => f p) h0 h1 h2

theorem coe_qP (k : Fin 4) : ((qP k : Pv) : Equiv.Perm (Fin N)) = qI sgen OPV.D k.val :=
  (q_eq k).symm

theorem coe_b1P : ((b1P : Pv) : Equiv.Perm (Fin N)) =
    qI sgen OPV.D 0 * qI sgen OPV.D 2 * (qI sgen OPV.D 0)⁻¹ * (qI sgen OPV.D 2)⁻¹ := by
  rw [b1P, commutatorElement_def]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [coe_qP 0, coe_qP 2]
  rfl

theorem wv_rW_q (e f : Nat) : wv (qI sgen OPV.D) (rW e f) =
    ((b1P ^ e * qP 2 ^ f : Pv) : Equiv.Perm (Fin N)) := by
  rw [wv_rW, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow, coe_b1P, coe_qP 2]
  rfl

theorem pl_pairs : ∀ i < 7, wv (qI sgen OPV.D) (wd (OPL.D (127 + 2 * i))) =
    wv (qI sgen OPV.D) (wd (OPL.D (128 + 2 * i))) :=
  plP_sound rp_on items_ok itemsE_ok sgen_mem7 sep_pv (P3' p_b0 p_b1 p_b2)

theorem pl_hd : wv (qI sgen OPV.D) (wd (OPL.D 134)) ≠ 1 ∧ qI sgen OPV.D 2 ≠ 1 :=
  plHd_sound rp_on items_ok itemsE_ok hd

theorem pl_b : b1P ≠ 1 ∧ qP 2 ≠ 1 ∧ b1P ^ 7 = 1 ∧ qP 2 ^ 7 = 1 ∧ b1P * qP 2 = qP 2 * b1P ∧
    qP 0 * b1P * (qP 0)⁻¹ = b1P ∧ qP 0 * qP 2 * (qP 0)⁻¹ = b1P * qP 2 ∧
    qP 1 * b1P * (qP 1)⁻¹ = b1P * qP 2 ∧ qP 1 * qP 2 * (qP 1)⁻¹ = qP 2 := by
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13⟩ := items_pairs
  have P := pl_pairs
  have p0 : wv (qI sgen OPV.D) (wd (OPL.D 127)) = wv (qI sgen OPV.D) (wd (OPL.D 128)) := P 0 (by omega)
  have p1 : wv (qI sgen OPV.D) (wd (OPL.D 129)) = wv (qI sgen OPV.D) (wd (OPL.D 130)) := P 1 (by omega)
  have p2 : wv (qI sgen OPV.D) (wd (OPL.D 131)) = wv (qI sgen OPV.D) (wd (OPL.D 132)) := P 2 (by omega)
  have p3 : wv (qI sgen OPV.D) (wd (OPL.D 133)) = wv (qI sgen OPV.D) (wd (OPL.D 134)) := P 3 (by omega)
  have p4 : wv (qI sgen OPV.D) (wd (OPL.D 135)) = wv (qI sgen OPV.D) (wd (OPL.D 136)) := P 4 (by omega)
  have p5 : wv (qI sgen OPV.D) (wd (OPL.D 137)) = wv (qI sgen OPV.D) (wd (OPL.D 138)) := P 5 (by omega)
  have p6 : wv (qI sgen OPV.D) (wd (OPL.D 139)) = wv (qI sgen OPV.D) (wd (OPL.D 140)) := P 6 (by omega)
  rw [i0, i1, wv_rW_q, wv_nil] at p0
  rw [i2, i3, wv_rW_q, wv_nil] at p1
  rw [i4, i5, wv_rW_q] at p2
  rw [i6, i7, wv_rW_q] at p3
  rw [i8, i9, wv_rW_q] at p4
  rw [i10, i11, wv_rW_q] at p5
  rw [i12, i13, wv_rW_q] at p6
  have hd := pl_hd
  rw [i7, wv_rW_q] at hd
  have c0 : qI sgen OPV.D 0 = ((qP 0 : Pv) : Equiv.Perm (Fin N)) := (q_eq 0).symm
  have c1 : qI sgen OPV.D 1 = ((qP 1 : Pv) : Equiv.Perm (Fin N)) := (q_eq 1).symm
  have c2 : qI sgen OPV.D 2 = ((qP 2 : Pv) : Equiv.Perm (Fin N)) := (q_eq 2).symm
  have hb := coe_b1P
  rw [c0, c2] at hb
  simp only [wv, lv, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at p2 p3 p4 p5 p6
  norm_num at p2 p3 p4 p5 p6
  simp only [c0, c1, c2] at p2 p3 p4 p5 p6
  rw [c2] at hd
  refine ⟨fun e => hd.1 ?_, fun e => hd.2 ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_,
    Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_, Subtype.ext ?_⟩
  · simp [e]
  · simp [e]
  · simpa using p0
  · simpa using p1
  all_goals
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, pow_one, pow_zero, one_mul,
      mul_one, hb] at p2 p3 p4 p5 p6 ⊢
  · simpa [mul_assoc] using p2
  · simpa [mul_assoc] using p3
  · simpa [mul_assoc] using p4
  · simpa [mul_assoc] using p5
  · simpa [mul_assoc] using p6

theorem blk {F : Nat → Nat → Bool} {lo cnt p : Nat} (h : allBlk lo (fun j => F j p) cnt = true)
    {j : Nat} (h1 : lo ≤ j) (h2 : j < lo + cnt) : F j p = true := by
  have := allBlk_spec h (j - lo) (by omega)
  rwa [show Nat.add lo (j - lo) = j by simp only [Nat.add_eq]; omega] at this

theorem ln_at {j : Nat} (hj : j < 14) :
    ∀ p ∈ [(⟨0, by decide⟩ : Fin 245520), ⟨227759, by decide⟩, ⟨100817, by decide⟩],
      plLn ON.TT ON.UU OPV.D OPL.D j p = true := by
  rcases Nat.lt_or_ge j 7 with h | h
  · have a1 : (0 : Nat) ≤ j := by omega
    have a2 : j < 0 + 7 := by omega
    exact P3' (f := fun p => plLn ON.TT ON.UU OPV.D OPL.D j p)
      (blk (F := fun j p => plLn ON.TT ON.UU OPV.D OPL.D j p) ln_b0a a1 a2)
      (blk (F := fun j p => plLn ON.TT ON.UU OPV.D OPL.D j p) ln_b1a a1 a2)
      (blk (F := fun j p => plLn ON.TT ON.UU OPV.D OPL.D j p) ln_b2a a1 a2)
  · have a1 : (7 : Nat) ≤ j := by omega
    have a2 : j < 7 + 7 := by omega
    exact P3' (f := fun p => plLn ON.TT ON.UU OPV.D OPL.D j p)
      (blk (F := fun j p => plLn ON.TT ON.UU OPV.D OPL.D j p) ln_b0b a1 a2)
      (blk (F := fun j p => plLn ON.TT ON.UU OPV.D OPL.D j p) ln_b1b a1 a2)
      (blk (F := fun j p => plLn ON.TT ON.UU OPV.D OPL.D j p) ln_b2b a1 a2)

theorem al_at {j : Nat} (hj1 : 14 ≤ j) (hj : j < 28) :
    ∀ p ∈ [(⟨0, by decide⟩ : Fin 245520), ⟨227759, by decide⟩, ⟨100817, by decide⟩],
      plAl ON.TT ON.UU OPV.D OPL.D j p = true := by
  rcases Nat.lt_or_ge j 21 with h | h
  · have a1 : (14 : Nat) ≤ j := by omega
    have a2 : j < 14 + 7 := by omega
    exact P3' (f := fun p => plAl ON.TT ON.UU OPV.D OPL.D j p)
      (blk (F := fun j p => plAl ON.TT ON.UU OPV.D OPL.D j p) al_b0a a1 a2)
      (blk (F := fun j p => plAl ON.TT ON.UU OPV.D OPL.D j p) al_b1a a1 a2)
      (blk (F := fun j p => plAl ON.TT ON.UU OPV.D OPL.D j p) al_b2a a1 a2)
  · have a1 : (21 : Nat) ≤ j := by omega
    have a2 : j < 21 + 7 := by omega
    exact P3' (f := fun p => plAl ON.TT ON.UU OPV.D OPL.D j p)
      (blk (F := fun j p => plAl ON.TT ON.UU OPV.D OPL.D j p) al_b0b a1 a2)
      (blk (F := fun j p => plAl ON.TT ON.UU OPV.D OPL.D j p) al_b1b a1 a2)
      (blk (F := fun j p => plAl ON.TT ON.UU OPV.D OPL.D j p) al_b2b a1 a2)

theorem coe_planeC {j : Nat} (hj : j < 28) :
    ((planeC j : Pv) : Equiv.Perm (Fin N)) = cI sgen OPV.D OPL.D j := by
  have hu := itemsE_h itemsE_ok (j := j) (by omega)
  have hm := itemsE_h itemsE_ok (j := 28 + j) (by omega)
  rw [items_pl.1 j hj] at hu
  rw [items_pl.2.1 j hj] at hm
  simp only [planeC, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [cI, items_pl.1 j hj, items_pl.2.1 j hj, wv_hI hm, evalS,
    evalWord_eq_wv sgen (Lm_mono (by omega) hu)]

theorem coe_onLine {i : Nat} (hi : i < 57) :
    ((onLine i : Pv) : Equiv.Perm (Fin N)) = gI sgen OPV.D (92 + i) := by
  have hl := items_hi items_ok (92 + i)
  rw [items_lines i hi] at hl
  change onSevenLine ⟨i % 57, _⟩ = _
  rw [show (⟨i % 57, Nat.mod_lt _ (by norm_num)⟩ : Fin 57) = ⟨i, hi⟩ from
    Fin.ext (Nat.mod_eq_of_lt hi), onSevenLine, gI, items_lines i hi, evalS,
    evalWord_eq_wv sgen hl]

theorem onLine_eq_hval {i k : Nat} (hi : i < 57) (hk : k < 15)
    (h : wv (hI sgen OPV.D) (wd (OPL.D (56 + k))) = gI sgen OPV.D (92 + i)) :
    onLine i = ⟨hval (wd (OPL.D (56 + k))), hval_mem _⟩ := by
  apply Subtype.ext
  rw [coe_onLine hi, ← h, wv_hI (itemsE_h itemsE_ok (j := 56 + k) (by omega))]

variable (α : Pv ≃* Pv) (hα0 : α ⟨a0, a0_mem⟩ = ⟨evalS alphaWordA, evalS_mem _⟩)
  (hα1 : α ⟨a1, a1_mem⟩ = ⟨a1, a1_mem⟩)

include hα0 hα1 in
theorem coe_alpha_pvS : ∀ k < 2, ((α (pvS k) : Pv) : Equiv.Perm (Fin N)) = aG sgen OPV.D k := by
  intro k hk
  interval_cases k
  · rw [pvS_zero, hα0]
    have h := items_hi items_ok 79
    rw [items_main.2.2.1] at h
    change evalS alphaWordA = aG sgen OPV.D 0
    rw [aG, if_pos rfl, gI, items_main.2.2.1, evalS, evalWord_eq_wv sgen h]
  · rw [pvS_one, hα1]
    change a1 = aG sgen OPV.D 1
    rw [aG, if_neg one_ne_zero]
    exact (cert_on_schreier_action_data.2.2.2.2.2.2.1).symm

include hα0 hα1 in
theorem coe_alpha_hgenP : ∀ k < 2, ((α (hgenP k) : Pv) : Equiv.Perm (Fin N)) = aI sgen OPV.D k := by
  intro k hk
  have hw7 := items_hi items_ok (77 + k)
  have hw2 := hA2 k hk
  have e : hgenP k = pvEval (wd (OPV.D (77 + k))) := by
    apply Subtype.ext
    interval_cases k
    · exact hgen_zero.trans (by rw [items_main.1]; rfl)
    · exact hgen_one.trans (by rw [items_main.2.1]; rfl)
  have m1 := map_evalWord α.toMonoidHom (fun h : Fin 7 => pvS h) (ptoLetters 7 (wd (OPV.D (77 + k))))
  have m2 := map_evalWord Pv.subtype (fun h : Fin 7 => α (pvS h))
    (ptoLetters 7 (wd (OPV.D (77 + k))))
  rw [e, pvEval_eq]
  refine ((congrArg Pv.subtype m1).trans m2).trans ?_
  refine (evalWord_eq_wv (fun k => ((α (pvS k) : Pv) : Equiv.Perm (Fin N))) hw7).trans ?_
  exact wv_congr (coe_alpha_pvS α hα0 hα1) hw2

include hα0 hα1 in
theorem coe_alpha_hval {w : List Int} (hw : Lm 2 w) :
    ((α ⟨hval w, hval_mem w⟩ : Pv) : Equiv.Perm (Fin N)) = wv (aI sgen OPV.D) w := by
  have m1 := map_evalWord α.toMonoidHom (fun h : Fin 2 => hgenP h) (ptoLetters 2 w)
  have m2 := map_evalWord Pv.subtype (fun h : Fin 2 => α (hgenP h)) (ptoLetters 2 w)
  rw [hP_eq]
  refine ((congrArg Pv.subtype m1).trans m2).trans ?_
  refine (evalWord_eq_wv (fun k => ((α (hgenP k) : Pv) : Equiv.Perm (Fin N))) hw).trans ?_
  exact wv_congr (coe_alpha_hgenP α hα0 hα1) hw

include hα0 hα1 in
theorem pl_lines : ∀ j < 28,
    (planeC j)⁻¹ * planeYA α j 0 * planeC j = b1P ^ planeE[j]!.1 * qP 2 ^ planeE[j]!.2.1 ∧
    (planeC j)⁻¹ * planeYA α j (j + 1) * planeC j =
      b1P ^ planeE[j]!.2.2.1 * qP 2 ^ planeE[j]!.2.2.2 := by
  intro j hj
  have hR := (items_pl.2.2.2 j hj)
  have hX := plX_sound rp_on items_ok itemsE_ok sgen_mem7 sep_pv (P3' x_b0 x_b1 x_b2)
  rcases Nat.lt_or_ge j 14 with h | h
  · obtain ⟨s1, s2⟩ := plLn_sound rp_on items_ok itemsE_ok sgen_mem7 sep_pv h (ln_at h)
    rw [hR.1, wv_rW_q] at s1
    rw [hR.2, wv_rW_q] at s2
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [planeYA, if_pos h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_planeC hj,
        coe_onLine (by norm_num)]
      exact s1
    · rw [planeYA, if_pos h, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_planeC hj,
        coe_onLine (by omega), show 92 + (j + 1) = 93 + j by omega]
      exact s2
  · obtain ⟨s1, s2⟩ := plAl_sound rp_on items_ok itemsE_ok sgen_mem7 hA2 sep_pv h hj (al_at h hj)
    rw [hR.1, wv_rW_q] at s1
    rw [hR.2, wv_rW_q] at s2
    have o0 : onLine 0 = ⟨hval (wd (OPL.D (56 + 0))), hval_mem _⟩ :=
      onLine_eq_hval (by norm_num) (by norm_num) hX.1
    have oj : onLine (j + 1) = ⟨hval (wd (OPL.D (56 + (j - 13)))), hval_mem _⟩ := by
      refine onLine_eq_hval (by omega) (by omega) ?_
      have := hX.2 (j - 14) (by omega)
      rwa [show 57 + (j - 14) = 56 + (j - 13) by omega,
        show 107 + (j - 14) = 92 + (j + 1) by omega] at this
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · rw [planeYA, if_neg (by omega), Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_planeC hj, o0, coe_alpha_hval α hα0 hα1 (itemsE_h itemsE_ok (by omega))]
      exact s1
    · rw [planeYA, if_neg (by omega), Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_planeC hj, oj, coe_alpha_hval α hα0 hα1 (itemsE_h itemsE_ok (by omega)),
        show 56 + (j - 13) = 43 + j by omega]
      exact s2

end Facts

end CertificateChecks.KernelSpor.ONPl

end
