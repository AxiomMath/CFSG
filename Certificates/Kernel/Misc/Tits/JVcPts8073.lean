
module

public import Certificates.Kernel.Misc.Tits.JFacts8073
public import Certificates.Kernel.Misc.Tits.JVc8073
public import Certificates.Kernel.Misc.Tits.JGrp8073

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.TitsJT.V

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Sporadic.Schreier.Tits
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelEvenBN CertificateChecks.KernelMisc.TitsJT
open scoped commutatorElement

theorem flat_get {α : Type} {m : ℕ} (g : ℕ → List α) (hg : ∀ a, (g a).length = m) :
    ∀ n a r, a < n → r < m → ((List.range n).flatMap g)[a * m + r]? = (g a)[r]? := by
  have hlen : ∀ n, ((List.range n).flatMap g).length = n * m := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp [hg, Nat.succ_mul]
  intro n
  induction n with
  | zero => intro a r ha; omega
  | succ n ih =>
    intro a r ha hr
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha' | rfl
    · rw [List.getElem?_append_left (by rw [hlen]; nlinarith)]
      exact ih a r ha' hr
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp

theorem lv : rcnt (TitsJ.LR 0) = 2 ∧ rcnt (TitsJ.LR 1) = 2 ∧ rcnt (TitsJ.LR 2) = 64 ∧
    rcnt (TitsJ.LR 3) = 2 := by
  have h := lvK
  simp only [CFSG.KS.bAnd_iff] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2.1,
    Nat.eq_of_beq_eq_true h.2.2.2⟩

theorem lev (k : ℕ) (hk : k < 4) :
    jLevels[k]!.pts.size = rcnt (TitsJ.LR k) ∧
      ∀ a < rcnt (TitsJ.LR k), canonK 1755 11 (mask 11) (1755 * 11) (tr k a) = true ∧
      (∀ x < 1755, (jLevels[k]!.tr[a]!)[x]! = pg 11 (mask 11) (tr k a) x) ∧
      ∃ σ, Rep 1755 jLevels[k]!.tr[a]! σ :=
  lev_trAt bindsJ permJ TitsJ.hl (i := k) hk

theorem idx_split {i : ℕ} (_hi : i < 512) :
    i = (i / 256) * 256 + ((i / 128 % 2) * 128 + ((i / 2 % 64) * 2 + i % 2)) := by omega

theorem table4_get (L : Array Level) (h0 : L[0]!.pts.size = 2) (h1 : L[1]!.pts.size = 2)
    (h2 : L[2]!.pts.size = 64) (h3 : L[3]!.pts.size = 2) {i : ℕ} (hi : i < 512) :
    (table4 1755 L)[i]! = compA 1755 (compA 1755 (compA 1755 L[0]!.tr[i / 256]!
      L[1]!.tr[i / 128 % 2]!) L[2]!.tr[i / 2 % 64]!) L[3]!.tr[i % 2]! := by
  unfold table4
  rw [h0, h1, h2, h3, getElem!_def, List.getElem?_toArray]
  conv_lhs => rw [idx_split hi]
  rw [flat_get (m := 256) _ (fun a => by simp) 2 _ _ (by omega) (by omega),
    flat_get (m := 128) _ (fun b => by simp) 2 _ _ (by omega) (by omega),
    flat_get (m := 2) _ (fun c => by simp) 64 _ _ (by omega) (by omega)]
  simp only [List.getElem?_map, List.getElem?_range (show i % 2 < 2 by omega), Option.map_some]

theorem jPel_get {i : ℕ} (hi : i < 512) : jPel[i]! =
    compA 1755 (compA 1755 (compA 1755 jLevels[0]!.tr[i / 256]! jLevels[1]!.tr[i / 128 % 2]!)
      jLevels[2]!.tr[i / 2 % 64]!) jLevels[3]!.tr[i % 2]! :=
  table4_get jLevels ((lev 0 (by omega)).1.trans lv.1) ((lev 1 (by omega)).1.trans lv.2.1)
    ((lev 2 (by omega)).1.trans lv.2.2.1) ((lev 3 (by omega)).1.trans lv.2.2.2) hi

theorem tr_facts {k a : ℕ} (hk : k < 4) (ha : a < rcnt (TitsJ.LR k)) : Cn (tr k a) ∧
    ∀ x < 1755, (jLevels[k]!.tr[a]!)[x]! = pg 11 (mask 11) (tr k a) x :=
  ⟨((lev k hk).2 a ha).1, ((lev k hk).2 a ha).2.1⟩

theorem dec_lt {i : ℕ} (hi : i < 512) : i / 256 < rcnt (TitsJ.LR 0) ∧
    i / 128 % 2 < rcnt (TitsJ.LR 1) ∧ i / 2 % 64 < rcnt (TitsJ.LR 2) ∧ i % 2 < rcnt (TitsJ.LR 3) := by
  obtain ⟨l0, l1, l2, l3⟩ := lv
  rw [l0, l1, l2, l3]
  omega

theorem Pk_facts {i : ℕ} (hi : i < 512) : jPel[i]! = unpack 1755 11 (Pk i) ∧ Cn (Pk i) := by
  obtain ⟨d0, d1, d2, d3⟩ := dec_lt hi
  obtain ⟨k0, E0⟩ := tr_facts (by omega) d0
  obtain ⟨k1, E1⟩ := tr_facts (by omega) d1
  obtain ⟨k2, E2⟩ := tr_facts (by omega) d2
  obtain ⟨k3, E3⟩ := tr_facts (by omega) d3
  have e := (prod4_eq k0 k1 k2 k3 CertificateChecks.KernelSporSch.TitsCentral.canId E0 E1 E2 E3).1
  refine ⟨by rw [jPel_get hi, e]; rfl, ?_⟩
  exact cmpC (cmpC (cmpC (cmpC k0 k1) k2) k3) CertificateChecks.KernelSporSch.TitsCentral.canId

theorem Pk_rep {i : ℕ} (hi : i < 512) : Rep 1755 (unpack 1755 11 (Pk i)) (el i) := by
  rw [← (Pk_facts hi).1]
  exact el_rep hi

theorem finPt_coe (x : Fin 1755) : finPt 1755 (x : ℕ) = x := by
  rw [finPt_eq x.2]

theorem pt_eq {P : ℕ} {g : Equiv.Perm (Fin 1755)} (hr : Rep 1755 (unpack 1755 11 P) g) {p : ℕ}
    (hp : p < 1755) : pt P p = (g (finPt 1755 p) : ℕ) := by
  rw [pt, ← unpack_getT hp, rep_base hr p hp]

theorem X_eq {i p : ℕ} (hi : i < 512) (hp : p < 1755) : X i p = (el i (finPt 1755 p) : ℕ) := by
  obtain ⟨d0, d1, d2, d3⟩ := dec_lt hi
  have k0 := (tr_facts (by omega) d0).1
  have k1 := (tr_facts (by omega) d1).1
  have k2 := (tr_facts (by omega) d2).1
  have k3 := (tr_facts (by omega) d3).1
  have h := ((gpt_facts k0 k1 k2 k3 CertificateChecks.KernelSporSch.TitsCentral.canId).2 p hp).1
  have e : X i p = gpt 11 (mask 11) (tr 0 (i / 256)) (tr 1 (i / 128 % 2)) (tr 2 (i / 2 % 64))
      (tr 3 (i % 2)) (pidn 1755 11) p := rfl
  rw [e, ← h]
  change (unpack 1755 11 (Pk i))[p]! = _
  rw [rep_base (Pk_rep hi) p hp]

theorem onB_iff {f : ℕ → Bool} : onB f = true ↔ ∀ p ∈ titsJBase, f p = true := by
  unfold onB
  simp only [CFSG.KS.bAnd_iff, titsJBase, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq]

theorem onB_eq_iff {a b : Equiv.Perm (Fin 1755)} (ha : a ∈ titsJ) (hb : b ∈ titsJ) {fa fb : ℕ → ℕ}
    (hfa : ∀ p < 1755, fa p = a (finPt 1755 p)) (hfb : ∀ p < 1755, fb p = b (finPt 1755 p)) :
    onB (fun p => Nat.beq (fa p) (fb p)) = true ↔ a = b := by
  have hB : ∀ p ∈ titsJBase, p < 1755 := by
    intro p hp
    simp only [titsJBase, List.mem_cons, List.mem_nil_iff, or_false] at hp
    omega
  rw [onB_iff]
  constructor
  · intro h
    refine agree ha hb fun p hp => ?_
    have := h p hp
    rwa [Nat.beq_eq, hfa p (hB p hp), hfb p (hB p hp)] at this
  · rintro rfl p hp
    rw [Nat.beq_eq, hfa p (hB p hp), hfb p (hB p hp)]

theorem X_g {i : ℕ} (hi : i < 512) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) {p : ℕ} (hp : p < 1755) :
    X i (pt P p) = ((el i * g) (finPt 1755 p) : ℕ) := by
  rw [pt_eq hr hp, X_eq hi (g _).2, finPt_coe, Equiv.Perm.mul_apply]

theorem g_X {i : ℕ} (hi : i < 512) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) {p : ℕ} (hp : p < 1755) :
    pt P (X i p) = ((g * el i) (finPt 1755 p) : ℕ) := by
  rw [X_eq hi hp, pt_eq hr (el i _).2, finPt_coe, Equiv.Perm.mul_apply]

theorem cm_iff {i : ℕ} (hi : i < 512) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) (hg : g ∈ titsJ) :
    cm i P = true ↔ Commute (el i) g := by
  unfold cm
  exact onB_eq_iff (fa := fun p => X i (pt P p)) (fb := fun p => pt P (X i p))
    (mul_mem (el_mem hi) hg) (mul_mem hg (el_mem hi)) (fun p hp => X_g hi hr hp)
    (fun p hp => g_X hi hr hp)

theorem Z_rep : Rep 1755 (unpack 1755 11 Z) titsZ := by
  rw [← (wordEqK_sound derBind permD zW).1]
  exact titsZ_rep

theorem zc_iff {i : ℕ} (hi : i < 512) {P : ℕ} {g : Equiv.Perm (Fin 1755)}
    (hr : Rep 1755 (unpack 1755 11 P) g) (hg : g ∈ titsJ) :
    zc i P = true ↔ el i * g = titsZ * g * el i := by
  unfold zc
  refine onB_eq_iff (fa := fun p => X i (pt P p)) (fb := fun p => pt Z (pt P (X i p)))
    (mul_mem (el_mem hi) hg) (mul_mem (mul_mem z_mem hg) (el_mem hi))
    (fun p hp => X_g hi hr hp) (fun p hp => ?_)
  calc pt Z (pt P (X i p)) = pt Z ((g * el i) (finPt 1755 p) : ℕ) := congrArg (pt Z) (g_X hi hr hp)
    _ = (titsZ (finPt 1755 ((g * el i) (finPt 1755 p) : ℕ)) : ℕ) :=
        pt_eq Z_rep (((g * el i) (finPt 1755 p)).2)
    _ = ((titsZ * g * el i) (finPt 1755 p) : ℕ) := by
        rw [finPt_coe, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem sq_iff {i : ℕ} (hi : i < 512) : sq i = true ↔ el i * el i = 1 := by
  unfold sq
  exact onB_eq_iff (fa := fun p => X i (X i p)) (fb := fun p => p)
    (mul_mem (el_mem hi) (el_mem hi)) (one_mem _)
    (fun p hp => (congrArg (X i) (X_eq hi hp)).trans ((X_eq hi (el i _).2).trans (by
      rw [finPt_coe, Equiv.Perm.mul_apply])))
    (fun p hp => by rw [Equiv.Perm.one_apply, finPt_val hp])

theorem one_iff {i : ℕ} (hi : i < 512) : isOne i = true ↔ el i = 1 := by
  unfold isOne
  exact onB_eq_iff (fa := fun p => X i p) (fb := fun p => p) (el_mem hi) (one_mem _)
    (fun p hp => X_eq hi hp) (fun p hp => by rw [Equiv.Perm.one_apply, finPt_val hp])

theorem z_iff {i : ℕ} (hi : i < 512) : isZ i = true ↔ el i = titsZ := by
  unfold isZ
  exact onB_eq_iff (fa := fun p => X i p) (fb := fun p => pt Z p) (el_mem hi) z_mem
    (fun p hp => X_eq hi hp) (fun p hp => pt_eq Z_rep hp)

@[expose] noncomputable def sJ (k : ℕ) : Equiv.Perm (Fin 1755) := wordIn 13 titsT titsJWords[k]!

theorem sJ_rep {k : ℕ} (hk : k < 4) : Rep 1755 (unpack 1755 11 (TitsJ.S k)) (sJ k) := by
  have hj : k < titsJWords.length := by simpa [titsJWords] using hk
  obtain ⟨w1, -⟩ := (CFSG.KS.bAnd_iff _ _).1 (allN_spec wJ k hk)
  have es := (wordEqK_sound derBind permD w1).1
  have hl : lettersOK 13 titsJWords[k] = true := jWords_letters _ (List.getElem_mem _)
  rw [← es, sJ, getElem!_pos titsJWords k hj]
  exact rep_wordArr_titsT hl

@[expose] def SJ : Set (Equiv.Perm (Fin 1755)) := {g | ∃ w ∈ titsJWords, wordIn 13 titsT w = g}

theorem closure_SJ : Subgroup.closure SJ = titsJ := rfl

theorem mem_SJ {g : Equiv.Perm (Fin 1755)} : g ∈ SJ ↔ ∃ k < 4, sJ k = g := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hw
    refine ⟨k, by simpa [titsJWords] using hk, ?_⟩
    rw [sJ, getElem!_pos titsJWords k hk]
  · rintro ⟨k, hk, rfl⟩
    have hj : k < titsJWords.length := by simpa [titsJWords] using hk
    exact ⟨_, List.getElem_mem hj, by rw [sJ, getElem!_pos titsJWords k hj]⟩

theorem sJ_mem {k : ℕ} (hk : k < 4) : sJ k ∈ titsJ :=
  Subgroup.subset_closure (mem_SJ.2 ⟨k, hk, rfl⟩)

theorem cS {k : ℕ} (hk : k < 4) : Cn (TitsJ.S k) := (canK_at hk).2.2.2

theorem rep_unpack_eq {P Q : ℕ} {g h : Equiv.Perm (Fin 1755)} (hP : Rep 1755 (unpack 1755 11 P) g)
    (hQ : Rep 1755 (unpack 1755 11 Q) h) (e : P = Q) : g = h := by
  subst e
  exact hP.unique hQ

theorem zFacts : (∀ y ∈ Subgroup.closure SJ, Commute titsZ y) ∧ titsZ * titsZ = 1 ∧ titsZ ≠ 1 := by
  have h := zK
  simp only [CFSG.KS.bAnd_iff] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun y hy => ?_, ?_, fun e => ?_⟩
  · induction hy using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨k, hk, rfl⟩ := mem_SJ.1 hs
      have e := Nat.eq_of_beq_eq_true (allN_spec h1 k hk)
      refine rep_unpack_eq ?_ ?_ e
      · rw [← cmpU zC (cS hk)]
        exact rep_compA Z_rep (sJ_rep hk)
      · rw [← cmpU (cS hk) zC]
        exact rep_compA (sJ_rep hk) Z_rep
    | one => exact Commute.one_right _
    | mul y w _ _ py pw => exact py.mul_right pw
    | inv y _ py => exact py.inv_right
  · refine rep_unpack_eq ?_ ?_ (Nat.eq_of_beq_eq_true h2)
    · rw [← cmpU zC zC]
      exact rep_compA Z_rep Z_rep
    · rw [← CertificateChecks.KernelSporSch.TitsCentral.id_eq]
      exact rep_idA
  · have r1 : Rep 1755 (unpack 1755 11 (pidn 1755 11)) 1 := by
      rw [← CertificateChecks.KernelSporSch.TitsCentral.id_eq]
      exact rep_idA
    have := (eqA_iff Z_rep r1).2 e
    rw [eqU zC CertificateChecks.KernelSporSch.TitsCentral.canId] at this
    rw [this] at h3
    exact Bool.false_ne_true h3

@[expose] noncomputable def Esub : Subgroup (Equiv.Perm (Fin 1755)) := Grp.eSub zFacts.1 zFacts.2.1

theorem Pb_iff {i : ℕ} (hi : i < 512) : Pb i = true ↔ el i ∈ Esub := by
  rw [Esub, Grp.mem_eSub_iff zFacts.1 zFacts.2.1 (el_mem hi)]
  have hk : ∀ k < 4, (bIf(cm i (TitsJ.S k), true, zc i (TitsJ.S k))) = true ↔
      Grp.Z0 titsZ ⁅el i, sJ k⁆ := by
    intro k hk
    rw [Grp.Z0, commutatorElement_eq_one_iff_commute, ← cm_iff hi (sJ_rep hk) (sJ_mem hk)]
    have e2 : ⁅el i, sJ k⁆ = titsZ ↔ zc i (TitsJ.S k) = true := by
      rw [zc_iff hi (sJ_rep hk) (sJ_mem hk), commutatorElement_def]
      constructor
      · intro h
        rw [← h]
        group
      · intro h
        rw [h]
        group
    rw [e2]
    cases cm i (TitsJ.S k) <;> simp
  constructor
  · intro h s hs
    obtain ⟨k, hk', rfl⟩ := mem_SJ.1 hs
    exact (hk k hk').1 (allN_spec h k hk')
  · intro h
    exact allN_of_forall fun k hk' => (hk k hk').2 (h _ (mem_SJ.2 ⟨k, hk', rfl⟩))

theorem allc_iff {i : ℕ} (hi : i < 512) : allc i = true ↔ ∀ k < 4, Commute (el i) (sJ k) := by
  constructor
  · intro h k hk
    exact (cm_iff hi (sJ_rep hk) (sJ_mem hk)).1 (allN_spec h k hk)
  · intro h
    exact allN_of_forall fun k hk => (cm_iff hi (sJ_rep hk) (sJ_mem hk)).2 (h k hk)

end CertificateChecks.KernelMisc.TitsJT.V

end
