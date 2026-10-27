module

public import Certificates.Kernel.W4Row.HS119Glue

public section

set_option maxRecDepth 4000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.HS119 CFSG.KS.SporSch
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CertificateChecks.KernelSporSch

theorem eqB_iff {x y : Bool} : eqB x y = true ↔ x = y := by
  cases x <;> cases y <;> decide

theorem ofFn_congr32 {g h : ℕ → ℕ} (hgh : ∀ i < 32, g i = h i) : ofFn 32 g = ofFn 32 h := by
  rw [ofFn_eq, ofFn_eq]
  exact E_congr hgh

theorem e_zero : e 0 = 1 := by
  unfold e
  rw [eF_succ, if_pos rfl]

theorem e_om' {k : ℕ} (hk : k < 1024) {i : ℕ} (hi : i < 32) :
    e k (omF i hi) = omF (img (SE k) i) (img_lt _ _) :=
  Fin.ext (e_om hk hi)

theorem omF_val {i : ℕ} (hi : i < 32) : (omF i hi : ℕ) = Om i := rfl

theorem sq_of_comm {x y : Equiv.Perm (Fin 3850)} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y = y * x) : x * y * (x * y) = 1 := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [h]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

theorem comm_of_sq {x y : Equiv.Perm (Fin 3850)} (hx : x * x = 1) (hy : y * y = 1)
    (h : x * y * (x * y) = 1) : x * y = y * x := by
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right h
  rw [mul_inv_rev, hx', hy'] at h'
  exact h'.symm

theorem blt_false {a b : ℕ} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (Nat.blt_eq.mp hb) (by omega)

theorem pxK_lt {a b : ℕ} (hab : a < b) : pxK PT IX a b = IX (fd 16 (PT a) b) := by
  unfold pxK
  rw [blt_iff.2 hab]

theorem pxK_gt {a b : ℕ} (hab : b < a) : pxK PT IX a b = IX (fd 16 (PT b) a) := by
  unfold pxK
  rw [blt_false (Nat.le_of_lt hab), blt_iff.2 hab]

theorem pxK_self (a : ℕ) : pxK PT IX a a = 0 := by
  unfold pxK
  rw [blt_false le_rfl]

theorem inv_parts {k : ℕ} (hk : k < 1024) :
    IX k < 256 ∧ (mul 32 (SE k) (SE k) = SE 0 ↔ IX k < 192 ∧ II (IX k) = k) := by
  have h := (allN_iff _ _).1 s_inv k hk
  unfold CFSG.KC.HS119.invAt at h
  rw [letB_eq, andB_iff, blt_iff, eqB_iff, Bool.eq_iff_iff, beq_iff, andB_iff, blt_iff,
    beq_iff] at h
  exact h

section HS

theorem sq_iff {k : ℕ} (hk : k < 1024) : e k * e k = 1 ↔ IX k < 192 ∧ II (IX k) = k := by
  rw [← (inv_parts hk).2]
  constructor
  · intro h
    have himg : ∀ i < 32, img (SE k) (img (SE k) i) = i := by
      intro i hi
      have h1 := congrArg (fun x => (x (omF i hi) : ℕ)) h
      simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h1
      rw [e_om' hk hi, e_om hk (img_lt _ _), omF_val] at h1
      exact om_inj (img_lt _ _) hi h1
    rw [SE_zero]
    exact ofFn_congr32 himg
  · intro h
    rw [e_mul hk hk (by norm_num) h, e_zero]

noncomputable abbrev ι (a : ℕ) : Equiv.Perm (Fin 3850) := e (II a)

end HS

theorem ii_parts {a : ℕ} (ha : a < 192) : II a < 1024 ∧ IX (II a) = a := by
  have h := (allN_iff _ _).1 s_ii a ha
  unfold iiAt at h
  rw [letB_eq, andB_iff, blt_iff, beq_iff] at h
  exact h

theorem ii0 : II 0 = 0 := by decide +kernel

theorem ι_zero : ι 0 = 1 := by
  change e (II 0) = 1
  rw [ii0, e_zero]

theorem ι_inj {a b : ℕ} (ha : a < 192) (hb : b < 192) (h : ι a = ι b) : a = b := by
  have h1 := e_inj (ii_parts ha).1 (ii_parts hb).1 h
  rw [← (ii_parts ha).2, ← (ii_parts hb).2, h1]

section HS2

theorem ι_sq {a : ℕ} (ha : a < 192) : ι a * ι a = 1 := by
  obtain ⟨h1, h2⟩ := ii_parts ha
  exact (sq_iff h1).2 ⟨by rw [h2]; exact ha, by rw [h2]⟩

theorem ι_memS {a : ℕ} (ha : a < 192) : ι a ∈ hsS := e_memS (ii_parts ha).1

theorem exists_ι {x : Equiv.Perm (Fin 3850)} (hx : x ∈ hsS) (h2 : x * x = 1) :
    ∃ a < 192, x = ι a := by
  obtain ⟨k, hk, rfl⟩ := S_enum hx
  obtain ⟨h1, h3⟩ := (sq_iff hk).1 h2
  exact ⟨IX k, h1, by rw [ι, h3]⟩

theorem pair_all {a b : ℕ} (ha : a < 192) (hb : b < 192) : pairAt SE II PT a b = true := by
  have hr := fun {lo cnt : ℕ} (h : CFSG.KC.Misc.Clos.allR lo cnt
      (fun a => allN 192 (pairAt SE II PT a)) = true) (h1 : lo ≤ a) (h2 : a < lo + cnt) =>
    (allN_iff _ _).1 ((CFSG.KC.Misc.Clos.allR_iff _ _ _).1 h a h1 h2) b hb
  rcases Nat.lt_or_ge a 25 with h | h
  · exact hr s_pair0 (by omega) (by omega)
  rcases Nat.lt_or_ge a 54 with h' | h'
  · exact hr s_pair1 h (by omega)
  rcases Nat.lt_or_ge a 90 with h'' | h''
  · exact hr s_pair2 h' (by omega)
  · exact hr s_pair3 h'' (by omega)

theorem pair_spec {a b : ℕ} (ha : a < 192) (hb : b < 192) (hab : a < b) :
    fd 16 (PT a) b < 1024 ∧ ι a * ι b = e (fd 16 (PT a) b) := by
  have h := pair_all ha hb
  unfold pairAt at h
  rw [impB_iff] at h
  have h' := h (blt_iff.2 hab)
  rw [letB_eq, andB_iff, blt_iff, beq_iff] at h'
  exact ⟨h'.1, e_mul (ii_parts ha).1 (ii_parts hb).1 h'.1 h'.2⟩

theorem prod_spec {a b : ℕ} (ha : a < 192) (hb : b < 192) (hc : ι a * ι b = ι b * ι a) :
    pxK PT IX a b < 192 ∧ ι a * ι b = ι (pxK PT IX a b) := by
  rcases Nat.lt_trichotomy a b with hab | rfl | hab
  · obtain ⟨hm, he⟩ := pair_spec ha hb hab
    have hsq := sq_of_comm (ι_sq ha) (ι_sq hb) hc
    rw [he] at hsq
    obtain ⟨h1, h2⟩ := (sq_iff hm).1 hsq
    rw [pxK_lt hab]
    exact ⟨h1, by rw [he, ι, h2]⟩
  · rw [pxK_self, ι_sq ha, ι_zero]
    exact ⟨by norm_num, rfl⟩
  · obtain ⟨hm, he⟩ := pair_spec hb ha hab
    have hsq := sq_of_comm (ι_sq hb) (ι_sq ha) hc.symm
    rw [he] at hsq
    obtain ⟨h1, h2⟩ := (sq_iff hm).1 hsq
    rw [pxK_gt hab]
    exact ⟨h1, by rw [hc, he, ι, h2]⟩

theorem cm_of_comm {a b : ℕ} (ha : a < 192) (hb : b < 192) (hc : ι a * ι b = ι b * ι a) :
    (CM a).testBit b = true := by
  have h := (allN_iff _ _).1 ((allN_iff _ _).1 s_cm a ha) b hb
  unfold cmAt at h
  rw [eqB_iff, Bool.eq_iff_iff, bitB_iff, blt_iff] at h
  exact h.2 (prod_spec ha hb hc).1

end HS2

theorem ls_parts {R L : ℕ → ℕ} {j : ℕ} (hls : lsAt R L j = true) (hinc : lIncAt L j = true) :
    (∀ b, (R j).testBit b = true ↔ ∃ i < fd 8 (L j) 0, fd 8 (L j) (i + 1) = b) ∧
      ∀ i < fd 8 (L j) 0, fd 8 (L j) (i + 1) < 192 := by
  have hR : lMask (L j) = R j := Nat.eq_of_beq_eq_true hls
  refine ⟨fun b => by rw [← hR, lMask_testBit], fun i hi => ?_⟩
  unfold lIncAt at hinc
  rw [letB_eq, letB_eq, allN_iff] at hinc
  have := hinc i hi
  rw [andB_iff, blt_iff] at this
  exact this.1

theorem testBit_one (b : ℕ) : (1 : ℕ).testBit b = true ↔ b = 0 := by
  rw [show (1 : ℕ) = 2 ^ 0 by rfl, Nat.testBit_two_pow, decide_eq_true_iff, eq_comm]

theorem map_conj_mem {H : Subgroup (Equiv.Perm (Fin 3850))} {g y : Equiv.Perm (Fin 3850)} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨_, h, by group⟩

theorem closure_cons_mem {A : Subgroup (Equiv.Perm (Fin 3850))} (hA2 : ∀ a ∈ A, a * a = 1)
    {t : Equiv.Perm (Fin 3850)} {l : List (Equiv.Perm (Fin 3850))} (ht : t ∈ A)
    (hl : ∀ x ∈ l, x ∈ A) {y : Equiv.Perm (Fin 3850)} :
    y ∈ Subgroup.closure {x | x ∈ t :: l} ↔
      y ∈ Subgroup.closure {x | x ∈ l} ∨ t * y ∈ Subgroup.closure {x | x ∈ l} := by
  set X := Subgroup.closure {x | x ∈ l}
  have hXA : X ≤ A := (Subgroup.closure_le A).2 fun x hx => hl x hx
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    comm_of_sq (hA2 x hx) (hA2 y hy) (hA2 _ (A.mul_mem hx hy))
  have htt : t * t = 1 := hA2 t ht
  have hmemA : ∀ y, (y ∈ X ∨ t * y ∈ X) → y ∈ A := by
    rintro y (h | h)
    · exact hXA h
    · have := A.mul_mem ht (hXA h)
      rwa [← mul_assoc, htt, one_mul] at this
  let Y : Subgroup (Equiv.Perm (Fin 3850)) :=
    { carrier := {y | y ∈ X ∨ t * y ∈ X}
      mul_mem' := by
        intro x y hx hy
        have hxA := hmemA x hx
        rcases hx with h1 | h1 <;> rcases hy with h2 | h2
        · exact Or.inl (X.mul_mem h1 h2)
        · refine Or.inr ?_
          have e1 : t * (x * y) = x * (t * y) := by
            rw [← mul_assoc, hcomm t ht x hxA, mul_assoc]
          rw [e1]
          exact X.mul_mem h1 h2
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact X.mul_mem h1 h2
        · refine Or.inl ?_
          have e1 : (t * x) * (t * y) = x * y := by
            rw [hcomm t ht x hxA, mul_assoc, ← mul_assoc t t y, htt, one_mul]
          rw [← e1]
          exact X.mul_mem h1 h2
      one_mem' := Or.inl X.one_mem
      inv_mem' := by
        intro x hx
        rw [inv_eq_of_mul_eq_one_right (hA2 x (hmemA x hx))]
        exact hx }
  constructor
  · intro hy
    have hle : Subgroup.closure {x | x ∈ t :: l} ≤ Y := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Or.inr (by rw [htt]; exact X.one_mem)
      · exact Or.inl (Subgroup.subset_closure hx)
    exact hle hy
  · rintro (h | h)
    · exact Subgroup.closure_mono (fun x hx => List.mem_cons_of_mem _ hx) h
    · have h1 : t * y ∈ Subgroup.closure {x | x ∈ t :: l} :=
        Subgroup.closure_mono (fun x hx => List.mem_cons_of_mem _ hx) h
      have h2 : t ∈ Subgroup.closure {x | x ∈ t :: l} :=
        Subgroup.subset_closure (List.mem_cons_self)
      have := Subgroup.mul_mem _ h2 h1
      rwa [← mul_assoc, htt, one_mul] at this

end CFSG.KD.HS119

end
