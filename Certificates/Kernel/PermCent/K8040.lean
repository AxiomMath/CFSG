module

public import Certificates.Data.Kernel.PermCent.SmallF3TwinBase
public import CFSG.GH74.KGroups.L33Inputs
public import CFSG.Certificates.Kernel.PermCent.KGrpConjSound
public import Certificates.Data.Kernel.PermCent.L33Cov

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.SmallF3T.K8040

open CFSG.GH74.KGroups.L33 CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Certificates.Kernel.PkCV.KGrp CFSG.GH74.KGroups

section Conj

theorem any_congr_list {M : Type*} {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (p : M → Bool) :
    C.any p = D.any p := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  simp only [h]

theorem all_congr_list {M : Type*} {C D : List M} (h : ∀ x, x ∈ C ↔ x ∈ D) (p : M → Bool) :
    C.all p = D.all p := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [h]

variable {n : Nat} [Small n]

@[expose] noncomputable def o13B (LP : List (CV n)) (s b : CV n) : Bool :=
  bif !decide (b = s) && eq22C b s s b then order13PairC (centListC LP s) (centListC LP b) else true

@[expose] noncomputable def o13At (LA LP : List (CV n)) (s : CV n) : Bool :=
  bif decide ((centListC LP s).length = 48) then (invListC LA).all (o13B LP s) else true

theorem order13C_eq (LA LP : List (CV n)) : order13C LA LP = (invListC LA).all (o13At LA LP) :=
  rfl

theorem eq22C_conj (g x s : CV n) :
    eq22C (g * x * g⁻¹) (g * s * g⁻¹) (g * s * g⁻¹) (g * x * g⁻¹) = eq22C x s s x := by
  rw [eq22C_eq, eq22C_eq, decide_eq_decide]
  constructor
  · intro h
    calc x * s = g⁻¹ * ((g * x * g⁻¹) * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h]
      _ = s * x := by group
  · intro h
    calc (g * x * g⁻¹) * (g * s * g⁻¹) = g * (x * s) * g⁻¹ := by group
      _ = g * (s * x) * g⁻¹ := by rw [h]
      _ = (g * s * g⁻¹) * (g * x * g⁻¹) := by group

theorem powOneC_conj (g y : CV n) (k : Nat) : powOneC (g * y * g⁻¹) k = powOneC y k := by
  rw [powOneC_eq, powOneC_eq, conj_pow, decide_eq_decide, conj_eq_one_iff]

theorem decide_conj_eq (g x y : CV n) : decide (g * x * g⁻¹ = g * y * g⁻¹) = decide (x = y) := by
  rw [decide_eq_decide, mul_left_inj, mul_right_inj]

theorem invQ_conj (g y : CV n) :
    (powOneC (g * y * g⁻¹) 2 && !decide (g * y * g⁻¹ = 1)) = (powOneC y 2 && !decide (y = 1)) := by
  rw [powOneC_conj]
  congr 2
  rw [decide_eq_decide, conj_eq_one_iff]

variable {L : List (CV n)} {g : CV n}

theorem mem_filter_conj (h1 : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (h2 : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    (q q' : CV n → Bool) (hq : ∀ y, q (g * y * g⁻¹) = q' y) (x : CV n) :
    x ∈ L.filter q ↔ x ∈ (L.filter q').map fun y => g * y * g⁻¹ := by
  simp only [List.mem_filter, List.mem_map]
  constructor
  · rintro ⟨hx, e⟩
    refine ⟨g⁻¹ * x * g, ⟨h2 x hx, ?_⟩, by group⟩
    rw [← hq]
    have e' : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e']
    exact e
  · rintro ⟨y, ⟨hy, e⟩, rfl⟩
    exact ⟨h1 y hy, by rw [hq]; exact e⟩

theorem order13PairC_conj {C C' D D' : List (CV n)}
    (hC : ∀ x, x ∈ C ↔ x ∈ C'.map fun y => g * y * g⁻¹)
    (hD : ∀ x, x ∈ D ↔ x ∈ D'.map fun y => g * y * g⁻¹) :
    order13PairC C D = order13PairC C' D' := by
  unfold order13PairC
  rw [any_congr_list hC, List.any_map]
  congr 1
  funext c₁
  rw [Function.comp_apply, any_congr_list hD, List.any_map]
  congr 1
  funext c₂
  rw [Function.comp_apply]
  have e : g * c₁ * g⁻¹ * (g * c₂ * g⁻¹) = g * (c₁ * c₂) * g⁻¹ := by group
  rw [e, powOneC_conj, decide_eq_decide.2 conj_eq_one_iff]

theorem o13At_conj {LA LP : List (CV n)} (hA1 : ∀ x ∈ LA, g * x * g⁻¹ ∈ LA)
    (hA2 : ∀ x ∈ LA, g⁻¹ * x * g ∈ LA) (hP1 : ∀ x ∈ LP, g * x * g⁻¹ ∈ LP)
    (hP2 : ∀ x ∈ LP, g⁻¹ * x * g ∈ LP) (hnd : LP.Nodup) (s : CV n) :
    o13At LA LP (g * s * g⁻¹) = o13At LA LP s := by
  have hC : ∀ t x, x ∈ centListC LP (g * t * g⁻¹) ↔
      x ∈ (centListC LP t).map fun y => g * y * g⁻¹ := fun t =>
    mem_filter_conj hP1 hP2 _ _ fun y => eq22C_conj g y t
  have hlen : (centListC LP (g * s * g⁻¹)).length = (centListC LP s).length := by
    have hnd' : ((centListC LP s).map fun y => g * y * g⁻¹).Nodup :=
      (hnd.filter _).map fun a b h => by simpa using h
    have hnd1 : (centListC LP (g * s * g⁻¹)).Nodup := hnd.filter _
    exact ((List.perm_ext_iff_of_nodup hnd1 hnd').2 (hC s)).length_eq.trans (List.length_map _)
  have hI : ∀ x, x ∈ invListC LA ↔ x ∈ (invListC LA).map fun y => g * y * g⁻¹ :=
    mem_filter_conj hA1 hA2 _ _ fun y => invQ_conj g y
  unfold o13At
  rw [hlen, all_congr_list hI, List.all_map]
  congr 2
  funext b
  rw [Function.comp_apply]
  unfold o13B
  rw [decide_conj_eq, eq22C_conj, order13PairC_conj (hC s) (hC b)]

theorem all_drop {M : Type*} (l : List M) (p : M → Bool) (a k c : Nat) (h : a + k = c) :
    (l.drop a).all p = (((l.drop a).take k).all p && (l.drop c).all p) := by
  conv_lhs => rw [← List.take_append_drop k (l.drop a)]
  rw [List.all_append, List.drop_drop, ← h]

end Conj

@[expose] noncomputable def r0 : CV 26 := cOf PA

@[expose] noncomputable def r1 : CV 26 := cOf sg0 * cOf sg0 * cOf sg0

theorem kGen : siftC QP 1 0 = true ∧ siftC QP (cOf PA) 0 = true ∧ siftC QP (cOf PB) 0 = true := by
  decide +kernel

theorem kLen0 : (centListC (elemsC QP) r0).length = 48 := by decide +kernel

theorem kAt1 :o13At (elemsC QA) (elemsC QP) r1 = true := by decide +kernel

@[expose] noncomputable def wordP (w : List Nat) : CV 26 :=
  w.foldr (fun j x => [cOf PA, cOf PB].getD j 1 * x) 1

@[expose] noncomputable def rep (f : Nat) : CV 26 := bif Nat.beq f 0 then r0 else r1

@[expose] noncomputable def covAt (ok : Nat → Bool) (s : CV 26) : Bool :=
  cov.any fun e => Nat.beq s.1 e.1 && ok e.2.1 && eq22C (wordP e.2.2) (rep e.2.1) s (wordP e.2.2)

theorem covAt_conj {ok : Nat → Bool} {s : CV 26} (h : covAt ok s = true) :
    ∃ w f, ok f = true ∧ s = wordP w * rep f * (wordP w)⁻¹ := by
  obtain ⟨e, -, he⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, Bool.and_eq_true, eq22C_eq, decide_eq_true_iff] at he
  exact ⟨e.2.2, e.2.1, he.1.2, eq_mul_inv_of_mul_eq he.2.symm⟩

theorem wordP_mem (hP : ValidSchreier QP) (w : List Nat) : wordP w ∈ elemsC QP := by
  have hev : ∀ x, siftC QP x 0 = true → ev x ∈ QP.originalSubgroup := fun x hx =>
    (mem_iff_sift QP hP _).2 (by rw [sift_ev]; exact hx)
  rw [mem_elemsC QP hP]
  induction w with
  | nil => exact hev 1 kGen.1
  | cons j w ih =>
    change ev ([cOf PA, cOf PB].getD j 1 * wordP w) ∈ QP.originalSubgroup
    rw [← ev_mul']
    refine QP.originalSubgroup.mul_mem ?_ ih
    match j with
    | 0 => exact hev _ kGen.2.1
    | 1 => exact hev _ kGen.2.2
    | _ + 2 => exact hev 1 kGen.1

theorem kCovP : (invListC (elemsC QP)).all (covAt fun f => Nat.beq f 0) = true := by
  decide +kernel

theorem kCovA : (invListC (elemsC QA)).all (covAt fun _ => true) = true := by
  decide +kernel

theorem kB0 : (((invListC (elemsC QA)).drop 0).take 50).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kB1 : (((invListC (elemsC QA)).drop 50).take 50).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kB2 : (((invListC (elemsC QA)).drop 100).take 50).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kB3 : (((invListC (elemsC QA)).drop 150).take 50).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kB4 : (((invListC (elemsC QA)).drop 200).take 50).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kB5 : (((invListC (elemsC QA)).drop 250).take 50).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kB6 : ((invListC (elemsC QA)).drop 300).all (o13B (elemsC QP) r0) = true := by
  decide +kernel

theorem kAt0 : o13At (elemsC QA) (elemsC QP) r0 = true := by
  unfold o13At
  rw [kLen0, decide_eq_true (rfl : 48 = 48), Bool.cond_true,
    ← List.drop_zero (l := invListC (elemsC QA)), all_drop _ _ 0 50 50 rfl, kB0, Bool.true_and,
    all_drop _ _ 50 50 100 rfl, kB1, Bool.true_and, all_drop _ _ 100 50 150 rfl, kB2,
    Bool.true_and, all_drop _ _ 150 50 200 rfl, kB3, Bool.true_and, all_drop _ _ 200 50 250 rfl,
    kB4, Bool.true_and, all_drop _ _ 250 50 300 rfl, kB5, Bool.true_and, kB6]

theorem k8040 (hP : ValidSchreier QP) (hA : ValidSchreier QA)
    (hle : ∀ g ∈ elemsC QP, g ∈ elemsC QA) : fourGenC (elemsC QA) (elemsC QP) = true := by
  have hinv : ∀ g ∈ elemsC QP, g⁻¹ ∈ elemsC QP := fun g hg => by
    rw [mem_elemsC QP hP] at hg ⊢
    rw [← ev_inv']
    exact QP.originalSubgroup.inv_mem hg
  have hconj : ∀ g ∈ elemsC QP, ∀ s,
      o13At (elemsC QA) (elemsC QP) (g * s * g⁻¹) = o13At (elemsC QA) (elemsC QP) s := by
    intro g hg s
    have hg' := hinv g hg
    refine o13At_conj (fun x hx => conj_mem_elemsC QA hA (hle g hg) hx) (fun x hx => ?_)
      (fun x hx => conj_mem_elemsC QP hP hg hx) (fun x hx => ?_) (nodup_elemsC QP hP) s
    · have h := conj_mem_elemsC QA hA (hle _ hg') hx
      rwa [inv_inv] at h
    · have h := conj_mem_elemsC QP hP hg' hx
      rwa [inv_inv] at h
  unfold fourGenC
  rw [Bool.and_eq_true]
  constructor
  · unfold cent48C
    rw [List.all_eq_true]
    intro s hs
    obtain ⟨w, f, hf, rfl⟩ := covAt_conj (List.all_eq_true.1 kCovP s hs)
    rw [decide_eq_true_iff]
    refine (centL_conj QP hP (wordP_mem hP w) (rep f)).trans ?_
    rw [Nat.eq_of_beq_eq_true hf]
    exact kLen0
  · rw [order13C_eq, List.all_eq_true]
    intro s hs
    obtain ⟨w, f, -, rfl⟩ := covAt_conj (List.all_eq_true.1 kCovA s hs)
    rw [hconj _ (wordP_mem hP w)]
    unfold rep
    cases Nat.beq f 0
    · exact kAt1
    · exact kAt0

end CFSG.Certificates.Kernel.PkCV.SmallF3T.K8040

end
