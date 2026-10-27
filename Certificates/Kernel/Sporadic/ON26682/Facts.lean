module

public import Certificates.Kernel.Sporadic.ON26682.Checks
public import Certificates.Kernel.Sporadic.ON26682.OneClass
public import Certificates.Kernel.Sporadic.ONPv.Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON26682

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.ON26682 CFSG.KS.ONPv CFSG.KS.ONNQ CFSG.ONSchreier
  CertificateChecks.KernelSpor.ONPv CFSG.EvenSporadicStandard.Solomon78

theorem items26682_ok : (∀ j < 5, Lm 7 (wd (O26682.D j))) ∧ Lm 2 (wd (O26682.D 5)) ∧
    Lm 2 (wd (O26682.D 6)) ∧ (∀ k < 4, Lm 5 (wd (O26682.D (7 + k)))) ∧
    Lm 4 (wd (O26682.D 11)) ∧ Lm 4 (wd (O26682.D 12)) := by
  decide +kernel

theorem items26682_words : wd (O26682.D 0) = CFSG.ONSchreier.Data.LWords[0]! ∧
    wd (O26682.D 1) = CFSG.ONSchreier.Data.LWords[1]! ∧
    wd (O26682.D 2) = CFSG.ONSchreier.Data.zWord ∧
    wd (O26682.D 3) = CFSG.ONSchreier.Data.centerGeneratorWord ∧
    wd (O26682.D 7) = [1] ∧ wd (O26682.D 8) = [2] ∧ wd (O26682.D 9) = [5, 1, -5] ∧
    wd (O26682.D 10) = [5, 2, -5] := by
  decide +kernel

theorem lwords26682 : CFSG.ONSchreier.Data.LWords[0]! ∈ CFSG.ONSchreier.Data.LWords.toList ∧
    CFSG.ONSchreier.Data.LWords[1]! ∈ CFSG.ONSchreier.Data.LWords.toList := by
  decide +kernel

theorem pts26682 : ∀ p ∈ [(⟨0, by decide⟩ : Fin 245520), ⟨227759, by decide⟩, ⟨100817, by decide⟩],
    ch26682At ON.TT ON.UU O26682.D p = true := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ch26682_b0
  · exact ch26682_b1
  · exact ch26682_b2

section Kit


@[expose] noncomputable def e26 (k : Nat) : Equiv.Perm (Fin 245520) := wv sgen (wd (O26682.D k))

@[expose] noncomputable def x26 : Equiv.Perm (Fin 245520) := wv e26 (wd (O26682.D 5))

@[expose] noncomputable def g26 : Equiv.Perm (Fin 245520) := wv e26 (wd (O26682.D 6))

@[expose] noncomputable def f26 (k : Nat) : Equiv.Perm (Fin 245520) := wv e26 (wd (O26682.D (7 + k)))

theorem rp1_26682 : Rp (f1T ON.TT ON.UU O26682.D) (f1U ON.TT ON.UU O26682.D) e26 5 :=
  Rp_congr (itT_Rp (o := 0) rp_on fun k hk => items26682_ok.1 (0 + k) (by omega)) fun k _ => by
    simp only [e26, Nat.zero_add]

theorem rp2_26682 : Rp (f2T ON.TT ON.UU O26682.D) (f2U ON.TT ON.UU O26682.D) f26 4 :=
  itT_Rp (o := 7) rp1_26682 items26682_ok.2.2.2.1

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem pt26682 {p : Fin 245520} (h : ch26682At ON.TT ON.UU O26682.D p = true) :
    e26 3 (e26 3 p) = e26 2 p ∧ x26 (x26 p) = p ∧ g26 (x26 (g26⁻¹ p)) = x26 (e26 2 p) ∧
      e26 4 (e26 2 ((e26 4)⁻¹ p)) = e26 2 (x26 p) ∧
      wv f26 (wd (O26682.D 11)) p = sgen 0 p ∧ wv f26 (wd (O26682.D 12)) p = sgen 1 p := by
  have hR := rp1_26682
  have hx : Lm 5 (wd (O26682.D 5)) := Lm_mono (by omega) items26682_ok.2.1
  have hg : Lm 5 (wd (O26682.D 6)) := Lm_mono (by omega) items26682_ok.2.2.1
  have T : ∀ k < 5, ∀ y : Fin 245520, f1T ON.TT ON.UU O26682.D k y = (e26 k y : Nat) :=
    fun k hk y => (hR k hk y).1
  have U : ∀ k < 5, ∀ y : Fin 245520, f1U ON.TT ON.UU O26682.D k y = ((e26 k)⁻¹ y : Nat) :=
    fun k hk y => (hR k hk y).2
  have WX : ∀ y : Fin 245520, w1T ON.TT ON.UU O26682.D 5 y = (x26 y : Nat) :=
    fun y => iT_eq hR hx y
  have WG : ∀ y : Fin 245520, w1T ON.TT ON.UU O26682.D 6 y = (g26 y : Nat) :=
    fun y => iT_eq hR hg y
  have WGU : ∀ y : Fin 245520, w1U ON.TT ON.UU O26682.D 6 y = (g26⁻¹ y : Nat) :=
    fun y => iU_eq hR hg y
  unfold ch26682At ch26682Id ch26682Gen at h
  obtain ⟨hI, hG⟩ := (bAnd_iff _ _).1 h
  simp only [sB] at hI
  obtain ⟨a1, hI⟩ := (bAnd_iff _ _).1 hI
  obtain ⟨a2, hI⟩ := (bAnd_iff _ _).1 hI
  obtain ⟨a3, a4⟩ := (bAnd_iff _ _).1 hI
  obtain ⟨b1, b2⟩ := (bAnd_iff _ _).1 hG
  replace a1 := Nat.eq_of_beq_eq_true a1
  replace a2 := Nat.eq_of_beq_eq_true a2
  replace a3 := Nat.eq_of_beq_eq_true a3
  replace a4 := Nat.eq_of_beq_eq_true a4
  replace b1 := Nat.eq_of_beq_eq_true b1
  replace b2 := Nat.eq_of_beq_eq_true b2
  rw [T 3 (by omega) p, T 3 (by omega), T 2 (by omega) p] at a1
  rw [WX p, WX] at a2
  rw [WGU p, WX, WG, T 2 (by omega) p, WX] at a3
  rw [U 4 (by omega) p, T 2 (by omega), T 4 (by omega), WX p, T 2 (by omega)] at a4
  rw [iT_eq rp2_26682 items26682_ok.2.2.2.2.1 p, (rp_on 0 (by omega) p).1] at b1
  rw [iT_eq rp2_26682 items26682_ok.2.2.2.2.2 p, (rp_on 1 (by omega) p).1] at b2
  exact ⟨Fin.ext a1, Fin.ext a2, Fin.ext a3, Fin.ext a4, Fin.ext b1, Fin.ext b2⟩

theorem e26_mem : ∀ k < 5, e26 k ∈ Pv := fun k hk => wv_mem sgen_mem7 (items26682_ok.1 k hk)

theorem x26_mem : x26 ∈ Pv :=
  wv_mem (fun k hk => e26_mem k (by omega)) items26682_ok.2.1

theorem g26_mem : g26 ∈ Pv :=
  wv_mem (fun k hk => e26_mem k (by omega)) items26682_ok.2.2.1

theorem f26_mem : ∀ k < 4, f26 k ∈ Pv := fun k hk => wv_mem e26_mem (items26682_ok.2.2.2.1 k hk)

theorem sep26682 {a b : Equiv.Perm (Fin 245520)} (ha : a ∈ Pv) (hb : b ∈ Pv)
    (h : ∀ p : Fin 245520, ch26682At ON.TT ON.UU O26682.D p = true → a p = b p) : a = b :=
  sep_eq sep_pv ha hb fun p hp => h p (pts26682 p hp)

theorem mul_pt26682 {a b c : Equiv.Perm (Fin 245520)} (ha : a ∈ Pv) (hb : b ∈ Pv) (hc : c ∈ Pv)
    (h : ∀ p : Fin 245520, ch26682At ON.TT ON.UU O26682.D p = true → a (b p) = c p) :
    a * b = c :=
  sep26682 (Pv.mul_mem ha hb) hc fun p hp => h p hp

theorem sq_pt26682 {y : Equiv.Perm (Fin 245520)} (hy : y ∈ Pv)
    (h : ∀ p : Fin 245520, ch26682At ON.TT ON.UU O26682.D p = true → y (y p) = p) : y * y = 1 :=
  sep26682 (Pv.mul_mem hy hy) (one_mem Pv) fun p hp => h p hp

theorem conj_pt26682 {g y u v : Equiv.Perm (Fin 245520)} (hg : g ∈ Pv) (hy : y ∈ Pv)
    (hu : u ∈ Pv) (hv : v ∈ Pv)
    (h : ∀ p : Fin 245520, ch26682At ON.TT ON.UU O26682.D p = true → g (y (g⁻¹ p)) = u (v p)) :
    g * y * g⁻¹ = u * v :=
  sep26682 (Pv.mul_mem (Pv.mul_mem hg hy) (Pv.inv_mem hg)) (Pv.mul_mem hu hv) fun p hp => h p hp

theorem qq26682 : e26 3 * e26 3 = e26 2 :=
  mul_pt26682 (e26_mem 3 (by omega)) (e26_mem 3 (by omega)) (e26_mem 2 (by omega))
    fun _ hp => (pt26682 hp).1

theorem xx26682 : x26 * x26 = 1 := sq_pt26682 x26_mem fun _ hp => (pt26682 hp).2.1

theorem gx26682 : g26 * x26 * g26⁻¹ = x26 * e26 2 :=
  conj_pt26682 g26_mem x26_mem x26_mem (e26_mem 2 (by omega)) fun _ hp => (pt26682 hp).2.2.1

theorem cz26682 : e26 4 * e26 2 * (e26 4)⁻¹ = e26 2 * x26 :=
  conj_pt26682 (e26_mem 4 (by omega)) (e26_mem 2 (by omega)) (e26_mem 2 (by omega)) x26_mem
    fun _ hp => (pt26682 hp).2.2.2.1

theorem a0_26682 : wv f26 (wd (O26682.D 11)) = sgen 0 :=
  sep26682 (wv_mem f26_mem items26682_ok.2.2.2.2.1) (sgen_mem 0)
    fun p hp => (pt26682 hp).2.2.2.2.1

theorem a1_26682 : wv f26 (wd (O26682.D 12)) = sgen 1 :=
  sep26682 (wv_mem f26_mem items26682_ok.2.2.2.2.2) (sgen_mem 1)
    fun p hp => (pt26682 hp).2.2.2.2.2

theorem ids26682 : e26 3 * e26 3 = e26 2 ∧ x26 * x26 = 1 ∧ g26 * x26 * g26⁻¹ = x26 * e26 2 ∧
    e26 4 * e26 2 * (e26 4)⁻¹ = e26 2 * x26 ∧ wv f26 (wd (O26682.D 11)) = sgen 0 ∧
    wv f26 (wd (O26682.D 12)) = sgen 1 :=
  ⟨qq26682, xx26682, gx26682, cz26682, a0_26682, a1_26682⟩

theorem e26_evalS {k : Nat} (hk : k < 5) {w : List Int} (hw : wd (O26682.D k) = w) :
    e26 k = evalS w := by
  have hL := items26682_ok.1 k hk
  rw [hw] at hL
  rw [e26, hw, evalS, evalWord_eq_wv sgen hL]

theorem e26_two : e26 2 = onz := e26_evalS (by omega) items26682_words.2.2.1

theorem e26_three : e26 3 = onq := e26_evalS (by omega) items26682_words.2.2.2.1

theorem e26_memL : ∀ k < 2, e26 k ∈ onL := by
  intro k hk
  have h0 : e26 0 ∈ onL := by
    rw [e26_evalS (by omega) items26682_words.1]
    exact subset_closure (List.mem_map_of_mem lwords26682.1)
  have h1 : e26 1 ∈ onL := by
    rw [e26_evalS (by omega) items26682_words.2.1]
    exact subset_closure (List.mem_map_of_mem lwords26682.2)
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact h0
  · exact h1

theorem x26_memL : x26 ∈ onL := wv_mem e26_memL items26682_ok.2.1

theorem g26_memL : g26 ∈ onL := wv_mem e26_memL items26682_ok.2.2.1

theorem f26_memLLc : ∀ k < 4, f26 k ∈ onL ⊔ onL.map (MulAut.conj (e26 4)).toMonoidHom := by
  have w := items26682_words
  intro k hk
  obtain rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  · have e : f26 0 = e26 0 := by simp [f26, w.2.2.2.2.1, wv, lv]
    rw [e]
    exact mem_sup_left (e26_memL 0 (by omega))
  · have e : f26 1 = e26 1 := by simp [f26, w.2.2.2.2.2.1, wv, lv]
    rw [e]
    exact mem_sup_left (e26_memL 1 (by omega))
  · have e : f26 2 = e26 4 * e26 0 * (e26 4)⁻¹ := by
      simp [f26, w.2.2.2.2.2.2.1, wv, lv, mul_assoc]
    rw [e]
    exact mem_sup_right ⟨e26 0, e26_memL 0 (by omega), rfl⟩
  · have e : f26 3 = e26 4 * e26 1 * (e26 4)⁻¹ := by
      simp [f26, w.2.2.2.2.2.2.2, wv, lv, mul_assoc]
    rw [e]
    exact mem_sup_right ⟨e26 1, e26_memL 1 (by omega), rfl⟩

theorem pv_le26682 : Pv ≤ onL ⊔ onL.map (MulAut.conj (e26 4)).toMonoidHom := by
  have h0 := ids26682.2.2.2.2.1
  have h1 := ids26682.2.2.2.2.2
  rw [cert_on_schreier_action_data.2.2.2.2.2.1] at h0
  rw [cert_on_schreier_action_data.2.2.2.2.2.2.1] at h1
  rw [Pv, closure_le]
  rintro _ (rfl | rfl)
  · rw [← h0]
    exact wv_mem f26_memLLc items26682_ok.2.2.2.2.1
  · rw [← h1]
    exact wv_mem f26_memLLc items26682_ok.2.2.2.2.2

end Kit

theorem row26682 : onq * onq = onz ∧ ∃ x c : Equiv.Perm (Fin N), x ∈ onL ∧ x * x = 1 ∧ x ≠ 1 ∧
    x ∉ (center ↥onL).map onL.subtype ∧ c ∈ Pv ∧ c * onz * c⁻¹ = onz * x ∧
    Pv ≤ onL ⊔ onL.map (MulAut.conj c).toMonoidHom ∧ OneClassOutside onL := by
  obtain ⟨hqq, hxx, hgx, hcz, -, -⟩ := ids26682
  rw [e26_two, e26_three] at hqq
  rw [e26_two] at hgx hcz
  have hxc : x26 ∉ (center ↥onL).map onL.subtype := by
    rintro ⟨u, hu, hux⟩
    have hux' : (u : Equiv.Perm (Fin N)) = x26 := hux
    have hc : g26 * x26 = x26 * g26 := by
      have := congrArg Subtype.val (mem_center_iff.1 hu ⟨g26, g26_memL⟩)
      rwa [Subgroup.coe_mul, Subgroup.coe_mul, hux'] at this
    have hz : onz = 1 := by
      have e : x26 * onz = x26 * 1 := by rw [← hgx, hc, mul_one, mul_inv_cancel_right]
      exact mul_left_cancel e
    exact onz_ne_one hz
  have hx1 : x26 ≠ 1 := by
    intro h
    rw [h, mul_one, mul_inv_cancel, one_mul] at hgx
    exact onz_ne_one hgx.symm
  exact ⟨hqq, x26, e26 4, x26_memL, hxx, hx1, hxc, e26_mem 4 (by omega), hcz, pv_le26682,
    oneClass26682 hqq x26_memL hxx hxc g26_memL hgx⟩

end CertificateChecks.KernelSpor.ON26682

end
