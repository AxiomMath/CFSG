module

public import Certificates.Kernel.W4Row.HS119Cls
public import Certificates.Kernel.W4Row.HS119Ext

public section

set_option maxRecDepth 4000

namespace CFSG.KD.HS119

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.HS119 CFSG.KS.SporSch
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier CertificateChecks.KernelSporSch

theorem e_def (k : ℕ) : e k = eF SPA sg 9 k := rfl

theorem inv32' {i : ℕ} (hi : i < 32) {l : ℕ} (hl : l < 4) :
    img (SG l) (img (inv 32 (SG l)) i) = i := by
  obtain ⟨τ, hτ⟩ := exists_of_permK ((allN_iff _ _).1 s_perm l hl)
  rw [← hτ, code_inv (by norm_num), img_code' (by norm_num) τ⁻¹ hi]
  rw [vals_fin τ⁻¹ ⟨i, hi⟩, img_code (by norm_num) τ (τ⁻¹ ⟨i, hi⟩)]
  simp

theorem sg_inv_pt {l : ℕ} (hl : l < 4) {x : ℕ} (hx : x < 3850) :
    fd 12 (GIt l) (fd 12 (Gt l) x) = x := by
  have h := (sgI_rep hl).comp (sg_rep hl)
  rw [inv_mul_cancel] at h
  exact h x hx

theorem cg_parts {l a : ℕ} (hl : l < 4) (ha : a < 192) :
    fd 8 (CG l) a < 192 ∧ conj 32 (SG l) (SE (II a)) = SE (II (fd 8 (CG l) a)) := by
  have h := (allN_iff _ _).1 ((allN_iff _ _).1 s_cg l hl) a ha
  unfold cgAt at h
  rw [letB_eq, andB_iff, blt_iff, beq_iff] at h
  exact h

theorem conj_comm {g x y : Equiv.Perm (Fin 3850)}
    (h : g⁻¹ * x * g * (g⁻¹ * y * g) = g⁻¹ * y * g * (g⁻¹ * x * g)) : x * y = y * x := by
  calc x * y = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
    _ = y * x := by group

theorem ext_spec {inner : Bool} {PA : ℕ → ℕ} {gout : ℕ} {II PT IX CM CG R L XS : ℕ → ℕ}
    {nR j t : ℕ} (h : extAt inner PA gout II PT IX CM CG R L XS nR j t = true)
    (h1 : (R j).testBit t = false) (h2 : Nat.land (R j) (CM t) = R j)
    (h3 : inner = true → parK PA gout 9 (II t) = 0) :
    Nat.shiftRight (fd 32 (XS j) t) 10 < nR ∧
      (inner = true → parK PA gout 9 (Nat.land (fd 32 (XS j) t) 1023) = 0) ∧
      cMask PA CG PT IX (Nat.land (fd 32 (XS j) t) 1023) t (L j) =
        R (Nat.shiftRight (fd 32 (XS j) t) 10) := by
  unfold extAt at h
  rw [letB_eq, impB_iff] at h
  have hp : andB (notB (bitB (R j) t)) (andB (Nat.beq (Nat.land (R j) (CM t)) (R j))
      (impB inner (Nat.beq (parK PA gout 9 (II t)) 0))) = true := by
    rw [andB_iff, andB_iff, notB_iff, bitB_iff, h1, beq_iff, impB_iff, beq_iff]
    exact ⟨by decide, h2, h3⟩
  have h' := h hp
  rw [letB_eq, letB_eq, letB_eq, andB_iff, andB_iff, blt_iff, impB_iff, beq_iff, beq_iff] at h'
  exact h'

section HS


theorem eq_of_rep {x y : Equiv.Perm (Fin 3850)} (hx : x ∈ hsS) (hy : y ∈ hsS) {f g : ℕ → ℕ}
    (hf : RepF 3850 f x) (hg : RepF 3850 g y) (h : ∀ i < 32, f (Om i) = g (Om i)) : x = y := by
  refine eq_of_om hx hy fun i hi => Fin.ext ?_
  have h1 := hf (Om i) (om_lt hi)
  have h2 := hg (Om i) (om_lt hi)
  change ((x ⟨Om i, om_lt hi⟩ : Fin 3850) : ℕ) = y ⟨Om i, om_lt hi⟩
  rw [← h1, ← h2]
  exact h i hi

theorem cg_spec {l a : ℕ} (hl : l < 4) (ha : a < 192) :
    fd 8 (CG l) a < 192 ∧ sg l * ι a * (sg l)⁻¹ = ι (fd 8 (CG l) a) := by
  obtain ⟨hb, hc⟩ := cg_parts hl ha
  refine ⟨hb, ?_⟩
  have hka := (ii_parts ha).1
  have hkb := (ii_parts hb).1
  have hrep := (sg_rep hl).comp ((e_rep hka).comp (sgI_rep hl))
  rw [mul_assoc]
  refine eq_of_rep (hsS.mul_mem (sg_memS hl) (hsS.mul_mem (e_memS hka) (hsS.inv_mem (sg_memS hl))))
    (e_memS hkb) hrep (e_rep hkb) fun i hi => ?_
  have hj := img_lt (inv 32 (SG l)) i
  have e1 : fd 12 (GIt l) (Om i) = Om (img (inv 32 (SG l)) i) := by
    have e2 : Om i = fd 12 (Gt l) (Om (img (inv 32 (SG l)) i)) := by
      rw [rho l hl _ hj, inv32' hi hl]
    rw [e2, sg_inv_pt hl (om_lt hj)]
  beta_reduce
  rw [e1, evS_om SE_zero tree rho 9 _ hka (dep hka) _ hj, rho l hl _ (img_lt _ _),
    evS_om SE_zero tree rho 9 _ hkb (dep hkb) _ hi, ← hc]
  unfold conj
  rw [img_mul32 hi, img_mul32 hj]

theorem conjP_e {c a : ℕ} (hc : c < 1024) (ha : a < 192) :
    conjP SPA CG 9 c a < 192 ∧ e c * ι a * (e c)⁻¹ = ι (conjP SPA CG 9 c a) := by
  rw [e_def]
  exact conjP_spec (g := sg) (ι := ι) tree' (fun l hl a ha => cg_spec hl ha) 9 c hc (dep hc) a ha

theorem conjP_back {c a : ℕ} (hc : c < 1024) (ha : a < 192) :
    (e c)⁻¹ * ι (conjP SPA CG 9 c a) * e c = ι a := by
  rw [← (conjP_e hc ha).2]
  group

theorem cls_ind {inner : Bool} {R L XS : ℕ → ℕ} {nR : ℕ}
    (h0 : R 0 = 1) (hn : 0 < nR)
    (hls : ∀ j < nR, lsAt R L j = true) (hinc : ∀ j < nR, lIncAt L j = true)
    (hext : ∀ j < nR, ∀ t < 192, extAt inner SPA (GO 0) II PT IX CM CG R L XS nR j t = true)
    {A : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS) (hAP : inner = true → A ≤ hsP)
    (hA2 : ∀ a ∈ A, a * a = 1) :
    ∀ l : List (Equiv.Perm (Fin 3850)), (∀ x ∈ l, x ∈ A) →
      ∃ j < nR, ∃ g ∈ hsS, (inner = true → g ∈ hsP) ∧
        ∀ b < 192, ((R j).testBit b = true ↔ g⁻¹ * ι b * g ∈ Subgroup.closure {x | x ∈ l}) := by
  have hcA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    comm_of_sq (hA2 x hx) (hA2 y hy) (hA2 _ (A.mul_mem hx hy))
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨0, hn, 1, hsS.one_mem, fun _ => hsP.one_mem, fun b hb => ?_⟩
    have he : {x | x ∈ ([] : List (Equiv.Perm (Fin 3850)))} = ∅ := by
      ext x
      simp
    rw [h0, testBit_one, he, Subgroup.closure_empty, Subgroup.mem_bot, inv_one, one_mul, mul_one,
      ← ι_zero]
    exact ⟨fun h => by rw [h], fun h => ι_inj hb (by norm_num) h⟩
  | cons t l ih =>
    intro hl
    have htA : t ∈ A := hl t List.mem_cons_self
    have hlA : ∀ x ∈ l, x ∈ A := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    obtain ⟨j, hj, g, hg, hgP, h⟩ := ih hlA
    set X := Subgroup.closure {x | x ∈ l} with hX
    have hXA : X ≤ A := (Subgroup.closure_le A).2 fun x hx => hlA x hx
    have htS : g * t * g⁻¹ ∈ hsS := hsS.mul_mem (hsS.mul_mem hg (hAS htA)) (hsS.inv_mem hg)
    have htsq : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
      calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [hA2 t htA, mul_one, mul_inv_cancel]
    obtain ⟨τ, hτ, hτe⟩ := exists_ι htS htsq
    have htg : g⁻¹ * ι τ * g = t := by
      rw [← hτe]
      group
    obtain ⟨hLb, hLlt⟩ := ls_parts (hls j hj) (hinc j hj)
    have hcomm : ∀ x < 192, g⁻¹ * ι x * g ∈ A → ι τ * ι x = ι x * ι τ := fun x _ hx =>
      conj_comm (g := g) (by rw [htg]; exact hcA _ htA _ hx)
    by_cases hbit : (R j).testBit τ = true
    · have htX : t ∈ X := by
        rw [← htg]
        exact (h τ hτ).1 hbit
      refine ⟨j, hj, g, hg, hgP, fun b hb => ?_⟩
      rw [h b hb, closure_cons_mem hA2 htA hlA]
      constructor
      · exact Or.inl
      · rintro (h1 | h1)
        · exact h1
        · have h2 := X.mul_mem (X.inv_mem htX) h1
          rwa [← mul_assoc, inv_mul_cancel, one_mul] at h2
    · have hcm : Nat.land (R j) (CM τ) = R j := by
        apply Nat.eq_of_testBit_eq
        intro b
        change (R j &&& CM τ).testBit b = (R j).testBit b
        rw [Nat.testBit_and]
        cases hb : (R j).testBit b
        · simp
        · obtain ⟨i, hi, hib⟩ := (hLb b).1 hb
          have hb192 : b < 192 := hib ▸ hLlt i hi
          rw [cm_of_comm hτ hb192 (hcomm b hb192 (hXA ((h b hb192).1 hb)))]
          rfl
      have hinner : inner = true → parK SPA (GO 0) 9 (II τ) = 0 := fun hi =>
        (e_mem_iff (ii_parts hτ).1).1 (by
          change ι τ ∈ hsP
          rw [← hτe]
          exact hsP.mul_mem (hsP.mul_mem (hgP hi) (hAP hi htA)) (hsP.inv_mem (hgP hi)))
      obtain ⟨hj1, hc0, hcm'⟩ :=
        ext_spec (hext j hj τ hτ) (Bool.eq_false_iff.2 hbit) hcm hinner
      have hc : Nat.land (fd 32 (XS j) τ) 1023 < 1024 := land1023_lt _
      refine ⟨_, hj1, e (Nat.land (fd 32 (XS j) τ) 1023) * g, hsS.mul_mem (e_memS hc) hg,
        fun hi => hsP.mul_mem ((e_mem_iff hc).2 (hc0 hi)) (hgP hi), fun b hb => ?_⟩
      generalize Nat.land (fd 32 (XS j) τ) 1023 = c at hc hcm' ⊢
      have heq : (e c * g)⁻¹ * ι b * (e c * g) = g⁻¹ * ((e c)⁻¹ * ι b * e c) * g := by group
      rw [← hcm', cMask_testBit, closure_cons_mem hA2 htA hlA, heq]
      constructor
      · rintro ⟨i, hi, hb1 | hb1⟩
        · have hx := hLlt i hi
          have hxR := (hLb _).2 ⟨i, hi, rfl⟩
          left
          rw [← hb1, conjP_back hc hx]
          exact (h _ hx).1 hxR
        · have hx := hLlt i hi
          have hxR := (hLb _).2 ⟨i, hi, rfl⟩
          obtain ⟨hp, hpe⟩ := prod_spec hτ hx (hcomm _ hx (hXA ((h _ hx).1 hxR)))
          right
          rw [← hb1, conjP_back hc hp, ← hpe]
          have e3 : t * (g⁻¹ * (ι τ * ι (fd 8 (L j) (i + 1))) * g) =
              g⁻¹ * (ι τ * ι τ) * ι (fd 8 (L j) (i + 1)) * g := by
            rw [← htg]
            group
          rw [e3, ι_sq hτ, mul_one]
          exact (h _ hx).1 hxR
      · intro hy
        have hwS : (e c)⁻¹ * ι b * e c ∈ hsS :=
          hsS.mul_mem (hsS.mul_mem (hsS.inv_mem (e_memS hc)) (ι_memS hb)) (e_memS hc)
        have hwsq : (e c)⁻¹ * ι b * e c * ((e c)⁻¹ * ι b * e c) = 1 := by
          calc (e c)⁻¹ * ι b * e c * ((e c)⁻¹ * ι b * e c) = (e c)⁻¹ * (ι b * ι b) * e c := by
                group
            _ = 1 := by rw [ι_sq hb, mul_one, inv_mul_cancel]
        obtain ⟨x', hx', hwx⟩ := exists_ι hwS hwsq
        have hb' : b = conjP SPA CG 9 c x' := by
          refine ι_inj hb (conjP_e hc hx').1 ?_
          rw [← (conjP_e hc hx').2, ← hwx]
          group
        rw [hwx] at hy
        rcases hy with hy | hy
        · obtain ⟨i, hi, hix⟩ := (hLb x').1 ((h x' hx').2 hy)
          exact ⟨i, hi, Or.inl (by rw [hix, hb'])⟩
        · have hxA : g⁻¹ * ι x' * g ∈ A := by
            have h2 := A.mul_mem htA (hXA hy)
            rwa [← mul_assoc, hA2 t htA, one_mul] at h2
          obtain ⟨hp, hpe⟩ := prod_spec hτ hx' (hcomm x' hx' hxA)
          have hpX : g⁻¹ * ι (pxK PT IX τ x') * g ∈ X := by
            have e3 : g⁻¹ * (ι τ * ι x') * g = t * (g⁻¹ * ι x' * g) := by
              rw [← htg]
              group
            rw [← hpe, e3]
            exact hy
          obtain ⟨i, hi, hip⟩ := (hLb _).1 ((h _ hp).2 hpX)
          refine ⟨i, hi, Or.inr ?_⟩
          have hq := prod_spec hτ hp (hcomm _ hp (hXA hpX))
          have hqx : pxK PT IX τ (pxK PT IX τ x') = x' := by
            refine ι_inj hq.1 hx' ?_
            rw [← hq.2, ← hpe, ← mul_assoc, ι_sq hτ, one_mul]
          rw [hip, hqx, hb']

theorem cls_rep {inner : Bool} {R L XS : ℕ → ℕ} {nR : ℕ}
    (h0 : R 0 = 1) (hn : 0 < nR)
    (hls : ∀ j < nR, lsAt R L j = true) (hinc : ∀ j < nR, lIncAt L j = true)
    (hext : ∀ j < nR, ∀ t < 192, extAt inner SPA (GO 0) II PT IX CM CG R L XS nR j t = true)
    {A : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS) (hAP : inner = true → A ≤ hsP)
    (hA2 : ∀ a ∈ A, a * a = 1) :
    ∃ j < nR, ∃ g ∈ hsS, (inner = true → g ∈ hsP) ∧
      ∀ b < 192, ((R j).testBit b = true ↔ g⁻¹ * ι b * g ∈ A) := by
  classical
  have hfin := Set.toFinite (A : Set (Equiv.Perm (Fin 3850)))
  obtain ⟨j, hj, g, hg, hgP, h⟩ := cls_ind h0 hn hls hinc hext hAS hAP hA2
    hfin.toFinset.toList (fun x hx => by simpa using hx)
  have hset : {x | x ∈ hfin.toFinset.toList} = (A : Set (Equiv.Perm (Fin 3850))) := by
    ext x
    simp
  refine ⟨j, hj, g, hg, hgP, fun b hb => ?_⟩
  rw [h b hb, hset, Subgroup.closure_eq]

theorem clsS {A : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS) (hA2 : ∀ a ∈ A, a * a = 1) :
    ∃ j < 266, ∃ g ∈ hsS, ∀ b < 192, ((RS j).testBit b = true ↔ g⁻¹ * ι b * g ∈ A) := by
  have h0 : RS 0 = 1 := Nat.eq_of_beq_eq_true (andB_iff.1 x_r0).1
  have hls := (allN_iff _ _).1 (andB_iff.1 x_ls).1
  have hinc := (allN_iff _ _).1 (andB_iff.1 c_inc).1
  have hext : ∀ j < 266, ∀ t < 192,
      extAt false SPA (GO 0) II PT IX CM CG RS LS XS 266 j t = true := by
    intro j hj t ht
    have hr := fun {lo cnt : ℕ} (h : CFSG.KC.Misc.Clos.allR lo cnt (fun j => allN 192
        (extAt false SPA (GO 0) II PT IX CM CG RS LS XS 266 j)) = true) (h1 : lo ≤ j)
        (h2 : j < lo + cnt) =>
      (allN_iff _ _).1 ((CFSG.KC.Misc.Clos.allR_iff _ _ _).1 h j h1 h2) t ht
    rcases Nat.lt_or_ge j 70 with h | h
    · exact hr x_s0 (by omega) (by omega)
    rcases Nat.lt_or_ge j 140 with h' | h'
    · exact hr x_s1 h (by omega)
    · exact hr x_s2 h' (by omega)
  obtain ⟨j, hj, g, hg, -, h⟩ := cls_rep (inner := false) h0 (by norm_num) hls hinc hext hAS
    (fun h => absurd h (by decide)) hA2
  exact ⟨j, hj, g, hg, h⟩

theorem clsP {A : Subgroup (Equiv.Perm (Fin 3850))} (hAS : A ≤ hsS) (hAP : A ≤ hsP)
    (hA2 : ∀ a ∈ A, a * a = 1) :
    ∃ j < 56, ∃ g ∈ hsS, g ∈ hsP ∧ ∀ b < 192, ((RP j).testBit b = true ↔ g⁻¹ * ι b * g ∈ A) := by
  have h0 : RP 0 = 1 := Nat.eq_of_beq_eq_true (andB_iff.1 x_r0).2
  have hls := (allN_iff _ _).1 (andB_iff.1 x_ls).2
  have hinc := (allN_iff _ _).1 (andB_iff.1 c_inc).2
  have hext : ∀ j < 56, ∀ t < 192,
      extAt true SPA (GO 0) II PT IX CM CG RP LP XP 56 j t = true := fun j hj t ht =>
    (allN_iff _ _).1 ((allN_iff _ _).1 x_p j hj) t ht
  obtain ⟨j, hj, g, hg, hgP, h⟩ := cls_rep (inner := true) h0 (by norm_num) hls hinc hext hAS
    (fun _ => hAP) hA2
  exact ⟨j, hj, g, hg, hgP rfl, h⟩

end HS

end CFSG.KD.HS119

end
