module

public import Certificates.Kernel.NFMK.Checks
public import Certificates.Kernel.WEMK.Glue
public import CFSG.Certificates.Kernel.NFMKSound
public import CFSG.LocalAnalysis.StandardType.GGZSNFourInputs
import all CFSG.Certificates.Kernel.WEMKSound
import all CFSG.Certificates.Kernel.NFMKSound

public section

namespace CFSG.StandardType.ZS.NFMK

open Certificates.ExcModel Certificates.WEMK Certificates.HSMK Certificates.NFMK CFSG.KC.PCent
open CFSG.StandardType.ZS CFSG.StandardType.ZS.WEMK CFSG.StandardType.ZS.HSMK

local instance nfmk_factPrimeThirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem vinj {n : ℕ} {M : Subgroup (owEm_GL n)} {x y : ↥M} (h : (x.1 : Mat n) = (y.1 : Mat n)) : x = y :=
  Subtype.ext (Units.ext h)

theorem vmul {n : ℕ} {M : Subgroup (owEm_GL n)} (x y : ↥M) : ((x * y).1 : Mat n) = (x.1 : Mat n) * y.1 := rfl

theorem vone {n : ℕ} {M : Subgroup (owEm_GL n)} : ((1 : ↥M).1 : Mat n) = 1 := rfl

theorem vpow {n : ℕ} {M : Subgroup (owEm_GL n)} (x : ↥M) : ∀ k : ℕ, ((x ^ k).1 : Mat n) = (x.1 : Mat n) ^ k
  | 0 => rfl
  | k + 1 => by rw [pow_succ, vmul, vpow x k, pow_succ]

theorem vprod {n : ℕ} {M : Subgroup (owEm_GL n)} : ∀ w : List ↥M, ((w.prod).1 : Mat n) = (w.map fun x => (x.1 : Mat n)).prod
  | [] => rfl
  | a :: w => by rw [List.prod_cons, vmul, vprod w, List.map_cons, List.prod_cons]

theorem uset_le' {n : ℕ} {gens : Set (Mat n)} {V : List KPair}
    (hV : ∀ q ∈ V, ∃ u ∈ glClosure gens, (u : Mat n) = toM n (mat n q)) :
    Subgroup.closure (uset n V) ≤ glClosure gens := by
  rw [Subgroup.closure_le]
  rintro u ⟨q, hq, e⟩
  obtain ⟨u', hu', e'⟩ := hV q hq
  have : u = u' := Units.ext (by rw [e, e'])
  rw [SetLike.mem_coe, this]
  exact hu'

theorem conj_closure {M : Type*} [Monoid M] (A : M) (hA : A * A = 1) (Y L : Set M) (hL1 : (1 : M) ∈ L)
    (hLmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hY : ∀ y ∈ Y, A * y * A ∈ L) :
    ∀ z ∈ Submonoid.closure Y, A * z * A ∈ L := by
  intro z hz
  induction hz using Submonoid.closure_induction with
  | mem x hx => exact hY x hx
  | one => rw [mul_one, hA]; exact hL1
  | mul x y _ _ hx hy =>
    have e : A * (x * y) * A = (A * x * A) * (A * y * A) := by
      calc A * (x * y) * A = A * x * 1 * y * A := by simp only [mul_one, mul_assoc]
        _ = (A * x * A) * (A * y * A) := by rw [← hA]; simp only [mul_assoc]
    rw [e]
    exact hLmul _ hx _ hy

theorem sq_mem_of_conj {G : Type*} [Group G] (E : Subgroup G) [E.Normal] (s a c e : G) (hs : s * s = 1)
    (ha : a * a ∈ E) (he : e ∈ E) (h : s * a * s = c * e) : c * c ∈ E := by
  have h1 : (c * e) * (c * e) ∈ E := by
    have e1 : s * a * s * (s * a * s) = s * (a * a) * s⁻¹ := by
      rw [inv_eq_of_mul_eq_one_right hs]
      calc s * a * s * (s * a * s) = s * a * (s * s) * a * s := by group
        _ = s * (a * a) * s := by rw [hs]; group
    rw [← h, e1]
    exact Subgroup.Normal.conj_mem inferInstance _ ha s
  have h2 : c⁻¹ * e⁻¹ * c ∈ E := by
    have := Subgroup.Normal.conj_mem inferInstance _ (inv_mem he) c⁻¹
    rwa [inv_inv] at this
  have h3 : c * c = (c * e * (c * e)) * (e⁻¹ * (c⁻¹ * e⁻¹ * c)) := by group
  rw [h3]
  exact mul_mem h1 (mul_mem (inv_mem he) h2)

theorem ncard_four {α : Type*} {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ({a, b, c, d} : Set α).ncard = 4 := by
  have hna : a ∉ ({b, c, d} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h | h)
    · exact hab h
    · exact hac h
    · exact had h
  have hnb : b ∉ ({c, d} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · exact hbc h
    · exact hbd h
  have hnc : c ∉ ({d} : Set α) := by
    simp only [Set.mem_singleton_iff]
    exact hcd
  rw [show ({a, b, c, d} : Set α) = insert a (insert b (insert c ({d} : Set α))) by rfl]
  rw [Set.ncard_insert_of_notMem hna, Set.ncard_insert_of_notMem hnb,
    Set.ncard_insert_of_notMem hnc, Set.ncard_singleton]

theorem kGen_of_kCore {n : ℕ} {S : List NMat} {V : List KPair} {tab : List (List ℕ)} {par : List (ℕ × ℕ)}
    {wd : List (List ℕ)} {x0 t0 : ℕ} {tr : List (ℕ × ℕ)} {ord : List ℕ}
    (h : kCore n S V tab par wd x0 t0 tr ord = true) : kGen n S V tab par = true := by
  simp only [kCore, Bool.and_eq_true] at h
  simp only [kGen, Bool.and_eq_true]
  exact h.1.1

theorem toM_map_toN {n : ℕ} (L : List (M13 n)) {i : ℕ} (hi : i < L.length) :
    toM n ((L.map toN).getD i []) = (L.getD i (strict 1)).val := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, toM_toN, List.getD_eq_getElem _ _ hi]

theorem nf_model {m : ℕ} (gens : Set (Mat 4)) (S : List NMat) (hm : S.length = m) (h0 : 0 < m)
    (V : List KPair) (tab : List (List ℕ)) (par : List (ℕ × ℕ)) (hgen : kGen 4 S V tab par = true)
    (hTg : ∀ s < S.length, toM 4 (S.getD s []) ∈ gens) (hgX : ∀ g ∈ gens, ∃ i < V.length, Lm 4 V i = g)
    (E : List NMat) (Yi : List ℕ) (YW ET EN : List (List ℕ)) (Ep : List (ℕ × ℕ))
    (hel : kEl 4 S E (treeOf E) Yi YW ET EN Ep = true) (B : List ℕ) (CF : List (List ℕ)) (ZW IW : List ℕ)
    (hsp : (kSpan 4 E (treeOf E) B CF && kWords 4 S ZW IW) = true) (C : List NMat)
    (CT : List (List (ℕ × ℕ))) (CP : List (ℕ × ℕ)) (hcos : kCos 4 S E C (treeOf C) (treeOf E) CT CP = true)
    (OT : List (List ℕ)) (W : List (ℕ × List (ℕ × ℕ × ℕ)))
    (horb : kOrbT 4 S E C (treeOf C) (treeOf E) OT (W.map Prod.fst) = true)
    (hscan : kScan 4 E (treeOf C) C.length V W = true) (hpair : kPairO 4 V = true)
    (lv : List (List ℕ × (List (List ℕ × List ℕ) × List KPair))) (hchain : kChain 4 V lv = true)
    (zw : List (Fin m)) (hzw : zw.map Fin.val = ZW) :
    ∃ t : Fin m → ↥(glClosure gens), (∀ i, ((t i).1 : Mat 4) = toM 4 (S.getD i [])) ∧ (∀ i, t i * t i = 1) ∧
      Subgroup.closure (Set.range t) = ⊤ ∧
      (lv.map fun l => l.2.1.length).prod ≤ Nat.card (glClosure gens) ∧
      (∀ N : Subgroup ↥(glClosure gens), N.Normal → N ≠ ⊥ → (zw.map t).prod ∈ N) ∧
      Nat.card (Subgroup.center ↥(glClosure gens)) = 4 ∧
      (∀ g h : ↥(glClosure gens), IsConj (t ⟨0, h0⟩) g → IsConj (t ⟨0, h0⟩) h → orderOf (g * h) ≤ 4) ∧
      ∀ g : ↥(glClosure gens), g * g = 1 → Forms (t ⟨0, h0⟩) (zw.map t).prod g := by
  obtain ⟨hSf, hM, hVin⟩ := gen_sound hgen (by omega) gens hTg hgX
  have hS : ∀ s ∈ S, WF 4 s := fun s hs => (hSf s hs).1
  have hlt : ∀ i : Fin m, (i : ℕ) < S.length := fun i => hm ▸ i.2
  have hinv : ∀ s < S.length, toM 4 (S.getD s []) * toM 4 (S.getD s []) = 1 := fun s hs =>
    (hSf _ (getD_mem_of_lt hs)).2
  let t : Fin m → ↥(glClosure gens) := fun i => ⟨owEm_unit _ (hinv i (hlt i)),
    Subgroup.subset_closure (by change toM 4 (S.getD i []) ∈ gens; exact hTg i (hlt i))⟩
  have ht : ∀ i, ((t i).1 : Mat 4) = toM 4 (S.getD i []) := fun i => rfl
  have htt : ∀ i, t i * t i = 1 := fun i => vinj (by rw [vmul, ht, hinv _ (hlt i), vone])
  have htinv : ∀ i, (t i)⁻¹ = t i := fun i => inv_eq_of_mul_eq_one_right (htt i)
  have htop : Subgroup.closure (Set.range t) = ⊤ := by
    have himage : (glClosure gens).subtype '' Set.range t =
        {g : owEm_GL 4 | ∃ s < S.length, (g : Mat 4) = toM 4 (S.getD s [])} := by
      ext x
      constructor
      · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, hlt i, ht i⟩
      · rintro ⟨s, hs, e⟩
        refine ⟨t ⟨s, hm ▸ hs⟩, ⟨_, rfl⟩, Units.ext ?_⟩
        rw [e]
        rfl
    apply Subgroup.map_injective (f := (glClosure gens).subtype) Subtype.val_injective
    rw [MonoidHom.map_closure, himage, Subgroup.map_top, Subgroup.range_subtype]
    exact hM.symm
  have hword : ∀ w : List ℕ, (∀ s ∈ w, s < S.length) →
      ∃ x : ↥(glClosure gens), (x.1 : Mat 4) = (w.map fun s => toM 4 (S.getD s [])).prod := by
    intro w
    induction w with
    | nil => exact fun _ => ⟨1, rfl⟩
    | cons s w ih =>
      intro hw
      obtain ⟨x, hx⟩ := ih fun a ha => hw a (List.mem_cons_of_mem _ ha)
      refine ⟨t ⟨s, hm ▸ hw s (by simp)⟩ * x, ?_⟩
      rw [vmul, hx, ht, List.map_cons, List.prod_cons]
  obtain ⟨hEpos, hE0, hEr, hY, hEcl, hEp, hEn⟩ := el_sound hel hS
  have hEwf : ∀ k < E.length, WF 4 (E.getD k []) := fun k hk => (hEr k hk).1.1
  have hEG : ∀ k < E.length, ∃ x : ↥(glClosure gens), (x.1 : Mat 4) = toM 4 (E.getD k []) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · exact ⟨1, by rw [vone, hE0]⟩
      obtain ⟨p, hpk, y, hy, he⟩ := hEp k hk (by omega)
      obtain ⟨x, hx⟩ := ih p hpk (by omega)
      obtain ⟨-, hys, hyw⟩ := hY y hy
      obtain ⟨u, hu⟩ := hword _ hys
      exact ⟨x * u, by rw [vmul, hx, hu, ← hyw, he]⟩
  let L : Set (Mat 4) := (fun k => toM 4 (E.getD k [])) '' {k | k < E.length}
  let Y : Set (Mat 4) := {A | ∃ y < Yi.length, toM 4 (E.getD (Yi.getD y 0) []) = A}
  have hL1 : (1 : Mat 4) ∈ L := ⟨0, hEpos, hE0⟩
  have hLsub : L ⊆ Submonoid.closure Y := by
    rintro A ⟨k, hk, rfl⟩
    exact tree_mem (fun k => toM 4 (E.getD k [])) Y E.length hE0
      (fun k hk hk0 => by
        obtain ⟨p, hp, y, hy, e⟩ := hEp k hk hk0
        exact ⟨p, hp, _, ⟨y, hy, rfl⟩, e⟩) k hk
  have hclL : (Submonoid.closure Y : Set (Mat 4)) ⊆ L :=
    closure_sub L Y hL1 (by
      rintro x ⟨k, hk, rfl⟩ y ⟨j, hj, rfl⟩
      obtain ⟨k', hk', e⟩ := hEcl k hk j hj
      exact ⟨k', hk', e.symm⟩)
  have hLmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L := fun a ha b hb =>
    hclL (mul_mem (hLsub ha) (hLsub hb))
  have hL4 : ∀ a ∈ L, a ^ 4 = 1 := by
    rintro a ⟨k, hk, rfl⟩
    exact (hEr k hk).2
  let Es : Subgroup ↥(glClosure gens) :=
    { carrier := {x | (x.1 : Mat 4) ∈ L}
      mul_mem' := fun {a b} ha hb => by
        change ((a * b).1 : Mat 4) ∈ L
        rw [vmul]
        exact hLmul _ ha _ hb
      one_mem' := by
        change ((1 : ↥(glClosure gens)).1 : Mat 4) ∈ L
        rw [vone]
        exact hL1
      inv_mem' := fun {a} ha => by
        have h4 : a ^ 4 = 1 := vinj (by rw [vpow, vone]; exact hL4 _ ha)
        have e : a⁻¹ = a * a * a := inv_eq_of_mul_eq_one_right (by
          rw [← h4]
          simp only [pow_succ, pow_zero, one_mul, mul_assoc])
        change ((a⁻¹).1 : Mat 4) ∈ L
        rw [e, vmul, vmul]
        exact hLmul _ (hLmul _ ha _ ha) _ ha }
  have hEs : ∀ x : ↥(glClosure gens), x ∈ Es ↔ (x.1 : Mat 4) ∈ L := fun x => Iff.rfl
  have hconjL : ∀ s < S.length, ∀ a ∈ L, toM 4 (S.getD s []) * a * toM 4 (S.getD s []) ∈ L := by
    intro s hs a ha
    refine conj_closure _ (hinv s hs) Y L hL1 hLmul ?_ a (hLsub ha)
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k', hk', e⟩ := hEn s hs y hy
    exact ⟨k', hk', e.symm⟩
  have hgenN : ∀ i : Fin m, ∀ x ∈ Es, t i * x * t i ∈ Es := fun i x hx => by
    change ((t i * x * t i).1 : Mat 4) ∈ L
    rw [vmul, vmul, ht]
    exact hconjL i (hlt i) _ hx
  have hEsN : Es.Normal := by
    have hle : Subgroup.closure (Set.range t) ≤ Subgroup.normalizer (Es : Set ↥(glClosure gens)) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
      intro h
      rw [htinv i]
      constructor
      · exact hgenN i h
      · intro hh
        have := hgenN i _ hh
        rwa [show t i * (t i * h * t i) * t i = (t i * t i) * h * (t i * t i) by group, htt i, one_mul,
          mul_one] at this
    rw [htop] at hle
    exact ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_top g)) n).mp hn⟩
  have := hEsN
  have hLfin : L.Finite := (Set.finite_lt_nat E.length).image _
  have : Finite ↥Es := by
    have := hLfin.to_subtype
    exact Finite.of_injective (fun x : ↥Es => (⟨(x.1.1 : Mat 4), x.2⟩ : ↥L))
      (fun a b h => Subtype.ext (vinj (congrArg Subtype.val h)))
  have h4Es : ∀ e ∈ Es, e ^ 4 = 1 := fun e he => vinj (by rw [vpow, vone]; exact hL4 _ he)
  have hEgE : ∀ k < E.length, ∀ x : ↥(glClosure gens), (x.1 : Mat 4) = toM 4 (E.getD k []) → x ∈ Es :=
    fun k hk x hx => by
      change (x.1 : Mat 4) ∈ L
      rw [hx]
      exact ⟨k, hk, rfl⟩
  have hsp' := Bool.and_eq_true_iff.mp hsp
  have hspan := span_sound hsp'.1 (fun k hk => (hEr k hk).1)
  obtain ⟨-, hIWl, hZW, hIW⟩ := words_sound hsp'.2 hS
  have hscal : ∀ g : ↥(glClosure gens), (∀ e ∈ Es, Commute g e) →
      (g.1 : Mat 4) ∈ Set.range (Matrix.scalar (Fin 4)) := by
    intro g hg
    refine scalar_of_commute_span _ L hspan ?_
    rintro A ⟨k, hk, rfl⟩
    obtain ⟨x, hx⟩ := hEG k hk
    have hc := (hg x (hEgE k hk x hx)).eq
    change (g.1 : Mat 4) * toM 4 (E.getD k []) = toM 4 (E.getD k []) * g.1
    rw [← hx, ← vmul, ← vmul, hc]
  have hdet : ∀ x : ↥(glClosure gens), (x.1 : Mat 4).det ^ 2 = 1 := by
    suffices h : ∀ g : owEm_GL 4,
        g ∈ Subgroup.closure {g : owEm_GL 4 | ∃ s < S.length, (g : Mat 4) = toM 4 (S.getD s [])} →
        (g : Mat 4).det ^ 2 = 1 by
      intro x
      exact h x.1 (by rw [← hM]; exact x.2)
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨s, hs, e⟩ := hg
      rw [sq, ← Matrix.det_mul, e, hinv s hs, Matrix.det_one]
    | one => simp
    | mul a b _ _ ha hb => rw [Units.val_mul, Matrix.det_mul, mul_pow, ha, hb, one_mul]
    | inv a _ ha =>
      have e : ((a⁻¹ : owEm_GL 4) : Mat 4).det * (a : Mat 4).det = 1 := by
        rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
      have e2 := congrArg (· ^ 2) e
      simp only [mul_pow, ha, mul_one, one_pow] at e2
      exact e2
  have hdetsc : ∀ c : ZMod 13, (Matrix.scalar (Fin 4) c).det = c ^ 4 := fun c => by
    simp [Matrix.scalar_apply, Matrix.det_diagonal]
  have hscinj : ∀ a b : ZMod 13, Matrix.scalar (Fin 4) a = Matrix.scalar (Fin 4) b → a = b := fun a b h => by
    have := congrFun (congrFun h 0) 0
    simpa using this
  have hzv : (((zw.map t).prod).1 : Mat 4) = Matrix.scalar (Fin 4) (-1 : ZMod 13) := by
    rw [vprod, List.map_map, ← hZW, ← hzw, List.map_map]
    congr 1
  obtain ⟨iG, hiv⟩ := hword IW hIWl
  rw [hIW] at hiv
  have hscZ : ∀ x : ↥(glClosure gens), ∀ c, (x.1 : Mat 4) = Matrix.scalar (Fin 4) c →
      x ∈ Subgroup.center ↥(glClosure gens) := by
    intro x c hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply vinj
    rw [vmul, vmul, hx]
    exact (Matrix.scalar_commute c (fun r => mul_comm c r) _).eq.symm
  have hzc : ∀ x, Commute (zw.map t).prod x := fun x =>
    (Subgroup.mem_center_iff.mp (hscZ _ _ hzv) x).symm
  have hzz : (zw.map t).prod * (zw.map t).prod = 1 :=
    vinj (by rw [vmul, hzv, ← map_mul, show (-1 : ZMod 13) * -1 = 1 by decide, map_one, vone])
  have hnorm : ∀ N : Subgroup ↥(glClosure gens), N.Normal → N ≠ ⊥ → (zw.map t).prod ∈ N := by
    intro N hN hN0
    obtain ⟨c, hcN, hc1, l, hl⟩ :=
      exists_central_of_normal Es h4Es (fun g => (g.1 : Mat 4) ∈ Set.range (Matrix.scalar (Fin 4))) hscal N hN0
    have hd := hdet c
    rw [← hl, hdetsc] at hd
    have hl1 : l ≠ 1 := by
      rintro rfl
      apply hc1
      apply vinj
      rw [← hl, map_one, vone]
    rcases scalar_cases l hd hl1 with h | h
    · have e : c = (zw.map t).prod := vinj (by rw [← hl, hzv, h])
      rw [← e]
      exact hcN
    · have e : c * c = (zw.map t).prod := vinj (by rw [vmul, ← hl, hzv, ← map_mul, ← sq, h])
      rw [← e]
      exact mul_mem hcN hcN
  have hc4 : ∀ c : ZMod 13, (c ^ 4) ^ 2 = 1 → c = 1 ∨ c = -1 ∨ c = 5 ∨ c = -1 * 5 := by decide
  have hcen : Nat.card (Subgroup.center ↥(glClosure gens)) = 4 := by
    have hzi : (((zw.map t).prod * iG).1 : Mat 4) = Matrix.scalar (Fin 4) (-1 * 5) := by
      rw [vmul, hzv, hiv, map_mul]
    have hone : ((1 : ↥(glClosure gens)).1 : Mat 4) = Matrix.scalar (Fin 4) 1 := by rw [vone, map_one]
    have hset : (Subgroup.center ↥(glClosure gens) : Set ↥(glClosure gens)) =
        {1, (zw.map t).prod, iG, (zw.map t).prod * iG} := by
      ext x
      constructor
      · intro hx
        obtain ⟨l, hl⟩ := hscal x (fun e _ => (Subgroup.mem_center_iff.mp hx e).symm)
        have hd := hdet x
        rw [← hl, hdetsc] at hd
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases hc4 l hd with rfl | rfl | rfl | rfl
        · left; exact vinj (by rw [← hl, hone])
        · right; left; exact vinj (by rw [← hl, hzv])
        · right; right; left; exact vinj (by rw [← hl, hiv])
        · right; right; right; exact vinj (by rw [← hl, hzi])
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact hscZ _ _ hzv
        · exact hscZ _ _ hiv
        · exact hscZ _ _ hzi
    have hne : ∀ x y : ↥(glClosure gens), ∀ a b : ZMod 13, (x.1 : Mat 4) = Matrix.scalar (Fin 4) a →
        (y.1 : Mat 4) = Matrix.scalar (Fin 4) b → a ≠ b → x ≠ y := fun x y a b hx hy hab hxy =>
      hab (hscinj a b (by rw [← hx, ← hy, hxy]))
    have hnc : Nat.card ↥(Subgroup.center ↥(glClosure gens)) =
        ((Subgroup.center ↥(glClosure gens) : Set ↥(glClosure gens))).ncard := Nat.card_coe_set_eq _
    rw [hnc, hset]
    exact ncard_four (hne _ _ _ _ hone hzv (by decide)) (hne _ _ _ _ hone hiv (by decide))
      (hne _ _ _ _ hone hzi (by decide)) (hne _ _ _ _ hzv hiv (by decide)) (hne _ _ _ _ hzv hzi (by decide))
      (hne _ _ _ _ hiv hzi (by decide))
  have hgen' := hgen
  simp only [kGen, Bool.and_eq_true, decide_eq_true_eq] at hgen'
  obtain ⟨⟨⟨⟨-, hVpos⟩, hV0⟩, htab⟩, hpar⟩ := hgen'
  let t0 := t ⟨0, h0⟩
  have ht0 : (t0.1 : Mat 4) = Lm 4 V 0 := by
    change toM 4 (S.getD 0 []) = Lm 4 V 0
    rw [Lm, hV0]
  have ht00 : t0 * t0 = 1 := htt _
  have htabG : ∀ i < V.length, ∀ s : Fin m, (tab.getD i []).getD s 0 < V.length ∧
      ((t s).1 : Mat 4) * Lm 4 V i * (t s).1 = Lm 4 V ((tab.getD i []).getD s 0) := fun i hi s => by
    rw [ht]
    exact tab_sound htab hSf hi (hlt s)
  have hVc : ∀ i < V.length, ∃ c : ↥(glClosure gens), ((c * t0 * c⁻¹).1 : Mat 4) = Lm 4 V i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hi0 : i = 0
      · subst hi0
        exact ⟨1, by rw [one_mul, inv_one, mul_one, ht0]⟩
      obtain ⟨hp, hs, he⟩ := par_sound hpar i hi hi0
      obtain ⟨c, hc⟩ := ih _ hp (by omega)
      let s : Fin m := ⟨(par.getD i (0, 0)).2, hm ▸ hs⟩
      refine ⟨t s * c, ?_⟩
      rw [mul_inv_rev, htinv s, show t s * c * t0 * (c⁻¹ * t s) = t s * (c * t0 * c⁻¹) * t s by group,
        vmul, vmul, hc, (htabG _ (by omega) s).2]
      exact congrArg (Lm 4 V) he
  have hVinv : ∀ c : ↥(glClosure gens), (c * t0 * c⁻¹) * (c * t0 * c⁻¹) = 1 := fun c => by
    rw [show c * t0 * c⁻¹ * (c * t0 * c⁻¹) = c * (t0 * t0) * c⁻¹ by group, ht00, mul_one, mul_inv_cancel]
  let Vs : Set ↥(glClosure gens) := {g | ∃ i < V.length, (g.1 : Mat 4) = Lm 4 V i}
  have hVs_gen : ∀ s : Fin m, ∀ g ∈ Vs, t s * g * t s ∈ Vs := by
    rintro s g ⟨i, hi, e⟩
    exact ⟨_, (htabG i hi s).1, by rw [vmul, vmul, e, (htabG i hi s).2]⟩
  have hVs_conj : ∀ c : ↥(glClosure gens), ∀ g ∈ Vs, c⁻¹ * g * c ∈ Vs := by
    intro c
    have hc : c ∈ Subgroup.closure (Set.range t) := by rw [htop]; exact Subgroup.mem_top c
    induction hc using Subgroup.closure_induction_right with
    | one =>
      intro g hg
      simpa using hg
    | mul_right x _ s hs ih =>
      obtain ⟨i, rfl⟩ := hs
      intro g hg
      have := hVs_gen i _ (ih g hg)
      rwa [show t i * (x⁻¹ * g * x) * t i = (x * t i)⁻¹ * g * (x * t i) by
        rw [mul_inv_rev, htinv i]; group] at this
    | mul_inv_cancel x _ s hs ih =>
      obtain ⟨i, rfl⟩ := hs
      rw [htinv i]
      intro g hg
      have := hVs_gen i _ (ih g hg)
      rwa [show t i * (x⁻¹ * g * x) * t i = (x * t i)⁻¹ * g * (x * t i) by
        rw [mul_inv_rev, htinv i]; group] at this
  have hconjV : ∀ g, IsConj t0 g → g ∈ Vs := by
    intro g hg
    obtain ⟨c, rfl⟩ := isConj_iff.mp hg
    have := hVs_conj c⁻¹ t0 ⟨0, hVpos, ht0⟩
    rwa [inv_inv] at this
  have hpairs : ∀ g h : ↥(glClosure gens), IsConj t0 g → IsConj t0 h → orderOf (g * h) ≤ 4 := by
    refine orderOf_le_of_class t0 Vs hconjV ?_
    rintro r ⟨i, hi, e⟩
    obtain ⟨k, hk0, hk4, hpow⟩ := pair_sound hpair i hi
    exact ⟨k, hk0, hk4, vinj (by rw [vpow, vmul, ht0, e, hpow, vone])⟩
  have hcard : (lv.map fun l => l.2.1.length).prod ≤ Nat.card (glClosure gens) := by
    have hG : ∀ q ∈ V, ∃ u : owEm_GL 4, (u : Mat 4) = toM 4 (mat 4 q) := fun q hq => by
      obtain ⟨u, -, e⟩ := hVin q hq
      exact ⟨u, e⟩
    exact (chain_sound lv V hchain hG).trans (Nat.card_mono (Set.toFinite _) (uset_le' hVin))
  obtain ⟨hCpos, hC0, hCwf, hCT, hCP⟩ := cos_sound hcos hS hEwf hE0
  have hCG : ∀ i < C.length, ∃ x : ↥(glClosure gens), (x.1 : Mat 4) = toM 4 (C.getD i []) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, by rw [vone, hC0]⟩
      obtain ⟨p, hp, s, hs, e⟩ := hCP i hi (by omega)
      obtain ⟨x, hx⟩ := ih p hp (by omega)
      exact ⟨x * t ⟨s, hm ▸ hs⟩, by rw [vmul, hx, ht, e]⟩
  choose! Cg hCg using hCG
  choose! Eg hEg using hEG
  have hcov := cover_of_table Es (Set.range t) htop (by rintro _ ⟨i, rfl⟩; exact htt i) Cg C.length hCpos
    (vinj (by rw [hCg 0 hCpos, hC0, vone])) (by
      rintro i hi _ ⟨a, rfl⟩
      obtain ⟨j, hj, k, hk, e⟩ := hCT i hi a (hlt a)
      exact ⟨j, hj, Eg k, hEgE k hk _ (hEg k hk), vinj (by rw [vmul, vmul, hCg i hi, ht, e, hCg j hj, hEg k hk])⟩)
  have hsq : ∀ i < C.length, Cg i * Cg i ∈ Es →
      ∃ k < E.length, toM 4 (C.getD i []) * toM 4 (C.getD i []) = toM 4 (E.getD k []) := by
    intro i hi hF
    obtain ⟨k, hk, e⟩ := (hEs _).mp hF
    exact ⟨k, hk, by rw [← hCg i hi, ← vmul, ← e]⟩
  have hforms := forms_of_tree Es t0 (zw.map t).prod hzc Cg C.length hcov (fun i => Cg i * Cg i ∈ Es)
    (fun i => (OT.getD i []).getD 1 0) (fun i _ h => h) (by
      intro i hi hFi hd
      have hob := NFMK.orb_sound horb hS (fun k hk => (hEr k hk).1) hCwf i hi
      rcases hob.2 (hob.1 (hsq i hi hFi)) with ⟨h0', -⟩ | ⟨-, s, hs, c, hc, hdc, k, hk, e⟩
      · omega
      · have he : t ⟨s, hm ▸ hs⟩ * Cg i * t ⟨s, hm ▸ hs⟩ = Cg c * Eg k :=
          vinj (by rw [vmul, vmul, vmul, ht, hCg i hi, hCg c hc, hEg k hk]; exact e)
        exact ⟨t ⟨s, hm ▸ hs⟩, htt _, c, hc,
          sq_mem_of_conj Es _ _ _ _ (htt _) hFi (hEgE k hk _ (hEg k hk)) he, hdc, Eg k,
          hEgE k hk _ (hEg k hk), he⟩) (by
      intro i hi hFi hd e he hinv2
      have hob := NFMK.orb_sound horb hS (fun k hk => (hEr k hk).1) hCwf i hi
      have hroot : i ∈ W.map Prod.fst := by
        rcases hob.2 (hob.1 (hsq i hi hFi)) with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · omega
      obtain ⟨p, hpW, rfl⟩ := List.mem_map.mp hroot
      obtain ⟨-, hsc⟩ := scan_sound hscan (fun k hk => (hEr k hk).1) hCwf p hpW
      obtain ⟨k, hk, ek⟩ := (hEs e).mp he
      have hxv : ((Cg p.1 * e).1 : Mat 4) = toM 4 (C.getD p.1 []) * toM 4 (E.getD k []) := by
        rw [vmul, hCg _ hi, ← ek]
      have hk' := hsc k hk
      dsimp only at hk'
      rw [← hxv] at hk'
      rcases hk' with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, h⟩ | ⟨a, ha, b, hb, h⟩
      · exact absurd (by rw [← vmul, hinv2]; rfl) h
      · exact Or.inl (vinj (h.trans vone.symm))
      · obtain ⟨c, hc⟩ := hVc a ha
        exact Or.inr (Or.inl (isConj_iff.mpr ⟨c, vinj (hc.trans h.symm)⟩))
      · obtain ⟨c, hc⟩ := hVc a ha
        exact Or.inr (Or.inr (Or.inl (isConj_iff.mpr ⟨c, vinj (hc.trans (by rw [vmul, hzv, h]))⟩)))
      · obtain ⟨c, hc⟩ := hVc a ha
        obtain ⟨d, hd'⟩ := hVc b hb
        have hab : (c * t0 * c⁻¹) * (Cg p.1 * e) = d * t0 * d⁻¹ :=
          vinj (by rw [vmul (c * t0 * c⁻¹), hc, h, hd'])
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨c * t0 * c⁻¹, d * t0 * d⁻¹, isConj_iff.mpr ⟨c, rfl⟩,
          isConj_iff.mpr ⟨d, rfl⟩, ?_⟩)))
        rw [← hab, ← mul_assoc, hVinv, one_mul]
      · obtain ⟨c, hc⟩ := hVc a ha
        obtain ⟨d, hd'⟩ := hVc b hb
        have hab : (c * t0 * c⁻¹) * ((zw.map t).prod * (Cg p.1 * e)) = d * t0 * d⁻¹ :=
          vinj (by rw [vmul (c * t0 * c⁻¹), hc, vmul (zw.map t).prod, hzv, h, hd'])
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨c * t0 * c⁻¹, d * t0 * d⁻¹, isConj_iff.mpr ⟨c, rfl⟩,
          isConj_iff.mpr ⟨d, rfl⟩, ?_⟩)))
        rw [← hab, ← mul_assoc (c * t0 * c⁻¹) (c * t0 * c⁻¹), hVinv, one_mul, ← mul_assoc, hzz, one_mul])
  exact ⟨t, ht, htt, htop, hcard, hnorm, hcen, hpairs, hforms⟩

theorem isRefl_pi (g : owEm_GL 4) (hgg : (g : Mat 4) * (g : Mat 4) = 1) (hg : (g : Mat 4) = piMat 0 1 1) :
    IsReflMat g :=
  owEm_isReflMat_of_outer g hgg ![1, -1, 0, 0] ![-1, 1, 0, 0] (by decide) (by decide)
    (by rw [hg]; exact owEm_piMat_sub_one)

theorem five_inv : (5 : ZMod 13)⁻¹ = 8 := by
  have h5 : (5 : ZMod 13) ≠ 0 := by decide
  calc (5 : ZMod 13)⁻¹ = 1 * 5⁻¹ := by rw [one_mul]
    _ = (8 * 5) * 5⁻¹ := by rw [show (8 : ZMod 13) * 5 = 1 by decide]
    _ = 8 * (5 * 5⁻¹) := by rw [mul_assoc]
    _ = 8 * 1 := by rw [DivisionRing.mul_inv_cancel (5 : ZMod 13) h5]
    _ = 8 := by rw [mul_one]

theorem orderOf_unit (g h : owEm_GL 4) (hg : (g : Mat 4) = piMat 0 1 1) (hh : (h : Mat 4) = piMat 0 1 5) :
    orderOf (g * h) = 4 := by
  let D : Mat 4 := Matrix.diagonal fun i => if i = 0 ∨ i = 1 then -1 else 1
  have hDsq : D * D = 1 := by
    dsimp [D]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four] <;> decide
  let Du : owEm_GL 4 := owEm_unit D hDsq
  have hsqMat : (((g * h : owEm_GL 4) : Mat 4) ^ 2) = D := by
    rw [pow_two, Units.val_mul, hg, hh]
    dsimp [D]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [piMat, Matrix.mul_apply, Fin.sum_univ_four, five_inv] <;> decide
  have hsq : (g * h) ^ 2 = Du := by
    apply Units.ext
    change (((g * h : owEm_GL 4) : Mat 4) ^ 2) = D
    exact hsqMat
  have hDu : Du ^ 2 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    change (((Du : owEm_GL 4) : Mat 4) ^ 2) = 1
    rw [pow_two]; dsimp [Du]; exact hDsq
  have h4' : (g * h) ^ (2 * 2) = 1 := by
    rw [pow_mul, hsq, hDu]
  have h4 : (g * h) ^ 4 = 1 := by simpa using h4'
  have h2 : (g * h) ^ 2 ≠ 1 := by
    rw [hsq]
    intro hD
    have hmat := congrArg (fun u : owEm_GL 4 => (u : Mat 4)) hD
    have h00 := congrFun (congrFun hmat 0) 0
    dsimp [Du, D, owEm_unit] at h00
    have hne : (-1 : ZMod 13) ≠ 1 := by decide
    exact hne (by simpa using h00)
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using h4)

theorem orderOf_mul_gen {M : Subgroup (owEm_GL 4)} {g h : ↥M}
    (hg : ((g.1 : owEm_GL 4) : Mat 4) = piMat 0 1 1) (hh : ((h.1 : owEm_GL 4) : Mat 4) = piMat 0 1 5) :
    orderOf (g * h) = 4 := by
  have hcoe : ((g * h : ↥M) : owEm_GL 4) = g.1 * h.1 := rfl
  rw [← Subgroup.orderOf_coe (g * h), hcoe]
  exact orderOf_unit _ _ hg hh

theorem n4S_getD (i : Fin 4) :
    ((n4S ()).getD i (strict 1)).val = ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat] i := by
  fin_cases i <;> simp [n4S, owEm_strict]

theorem en4S_getD (i : Fin 5) :
    ((en4S ()).getD i (strict 1)).val =
      ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat, Matrix.diagonal fun j => if j = 3 then -1 else 1] i := by
  fin_cases i <;> simp [en4S, n4S, owEm_strict]

theorem nfmk_n4 :
    ∃ t : Fin 4 → ↥(model .N4),
      (∀ i, ((t i).1 : Matrix (Fin (mdeg .N4)) (Fin (mdeg .N4)) (ZMod 13)) =
        ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat] i) ∧
      Subgroup.closure (Set.range t) = ⊤ ∧ 7680 ≤ Nat.card (model .N4) ∧
      (∀ N : Subgroup ↥(model .N4), N.Normal → N ≠ ⊥ → (n4ZW.map t).prod ∈ N) ∧
      Nat.card (Subgroup.center ↥(model .N4)) = 4 ∧
      (∀ g h : ↥(model .N4), IsConj (t 0) g → IsConj (t 0) h → orderOf (g * h) ≤ 4) ∧
      (∀ g : ↥(model .N4), g * g = 1 → g = 1 ∨ IsConj (t 0) g ∨
        IsConj (t 0) ((n4ZW.map t).prod * g) ∨
        (∃ a b, IsConj (t 0) a ∧ IsConj (t 0) b ∧ g = a * b) ∨
        ∃ a b, IsConj (t 0) a ∧ IsConj (t 0) b ∧ g = (n4ZW.map t).prod * (a * b)) ∧
      IsReflMat (t 0).1 ∧ orderOf (t 0 * t 2) = 4 := by
  have h := Bool.and_eq_true_iff.mp CFSG.KD.WEMK.n4_ok
  obtain ⟨hSG, -⟩ := kCovN_sound h.2
  obtain ⟨hSg, hgX, -⟩ := covN_gens (n4S ()) n4Gens (by
      intro s hs
      simp only [n4S, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [n4Gens, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hs with rfl | rfl | rfl | rfl <;> simp [owEm_strict]) (by
      intro g hg
      simp only [n4Gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact ⟨strict (piMat 0 1 1), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 1 2 1), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 0 1 5), by simp [n4S], owEm_strict _⟩
      · exact ⟨strict aMat, by simp [n4S], owEm_strict _⟩) h.2
  obtain ⟨t, ht, htt, htop, hcard, hnorm, hcen, hpair, hforms⟩ := nf_model (m := 4) n4Gens
    CFSG.KD.WEMK.N4.S (by rw [hSG]; rfl) (by norm_num) _ _ _ (kGen_of_kCore h.1) hSg hgX _ _ _ _ _ _
    CFSG.KD.NFMK.n4_el _ _ _ _ CFSG.KD.NFMK.n4_span _ _ _ CFSG.KD.NFMK.n4_cos _ _ CFSG.KD.NFMK.n4_orb
    CFSG.KD.NFMK.n4_scan CFSG.KD.NFMK.n4_pair _ CFSG.KD.NFMK.n4_chain n4ZW (by decide +kernel)
  have hmat : ∀ i, ((t i).1 : Mat 4) = ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat] i := fun i => by
    rw [ht, hSG, toM_map_toN _ (by simp [n4S]), n4S_getD]
  have hrefl : IsReflMat (t 0).1 :=
    isRefl_pi _ (by rw [← vmul, htt, vone]) (by rw [hmat]; rfl)
  have hord : orderOf (t 0 * t 2) = 4 := orderOf_mul_gen (by rw [hmat]; rfl) (by rw [hmat]; rfl)
  have h7680 : 7680 ≤ Nat.card (glClosure n4Gens) := by
    rw [CFSG.KD.NFMK.n4_lens] at hcard
    exact hcard
  exact ⟨t, hmat, htop, h7680, hnorm, hcen, hpair, hforms, hrefl, hord⟩

theorem nfmk_en4 :
    ∃ t : Fin 5 → ↥(model .EN4),
      (∀ i, ((t i).1 : Matrix (Fin (mdeg .EN4)) (Fin (mdeg .EN4)) (ZMod 13)) =
        ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat,
          Matrix.diagonal fun j => if j = 3 then -1 else 1] i) ∧
      Subgroup.closure (Set.range t) = ⊤ ∧ 46080 ≤ Nat.card (model .EN4) ∧
      (∀ N : Subgroup ↥(model .EN4), N.Normal → N ≠ ⊥ → (en4ZW.map t).prod ∈ N) ∧
      Nat.card (Subgroup.center ↥(model .EN4)) = 4 ∧
      (∀ g h : ↥(model .EN4), IsConj (t 0) g → IsConj (t 0) h → orderOf (g * h) ≤ 4) ∧
      (∀ g : ↥(model .EN4), g * g = 1 → g = 1 ∨ IsConj (t 0) g ∨
        IsConj (t 0) ((en4ZW.map t).prod * g) ∨
        (∃ a b, IsConj (t 0) a ∧ IsConj (t 0) b ∧ g = a * b) ∨
        ∃ a b, IsConj (t 0) a ∧ IsConj (t 0) b ∧ g = (en4ZW.map t).prod * (a * b)) ∧
      IsReflMat (t 0).1 ∧ orderOf (t 0 * t 2) = 4 := by
  have h := Bool.and_eq_true_iff.mp CFSG.KD.WEMK.en4_ok
  obtain ⟨hSG, -⟩ := kCovN_sound h.2
  obtain ⟨hSg, hgX, -⟩ := covN_gens (en4S ()) en4Gens (by
      intro s hs
      simp only [en4S, n4S, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hs
      simp only [en4Gens, n4Gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hs with (rfl | rfl | rfl | rfl) | rfl
      · exact Or.inl (Or.inl (owEm_strict _))
      · exact Or.inl (Or.inr (Or.inl (owEm_strict _)))
      · exact Or.inl (Or.inr (Or.inr (Or.inl (owEm_strict _))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (owEm_strict _))))
      · exact Or.inr (owEm_strict _)) (by
      intro g hg
      simp only [en4Gens, n4Gens, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with (rfl | rfl | rfl | rfl) | rfl
      · exact ⟨strict (piMat 0 1 1), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 1 2 1), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (piMat 0 1 5), by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict aMat, by simp [en4S, n4S], owEm_strict _⟩
      · exact ⟨strict (Matrix.diagonal fun i => if i = 3 then -1 else 1),
          by unfold en4S; exact List.mem_append_right _ (List.mem_singleton_self _), owEm_strict _⟩) h.2
  obtain ⟨t, ht, htt, htop, hcard, hnorm, hcen, hpair, hforms⟩ := nf_model (m := 5) en4Gens
    CFSG.KD.WEMK.EN4.S (by rw [hSG]; rfl) (by norm_num) _ _ _ (kGen_of_kCore h.1) hSg hgX _ _ _ _ _ _
    CFSG.KD.NFMK.en4_el _ _ _ _ CFSG.KD.NFMK.en4_span _ _ _ CFSG.KD.NFMK.en4_cos _ _ CFSG.KD.NFMK.en4_orb
    CFSG.KD.NFMK.en4_scan CFSG.KD.NFMK.en4_pair _ CFSG.KD.NFMK.en4_chain en4ZW (by decide +kernel)
  have hmat : ∀ i, ((t i).1 : Mat 4) = ![piMat 0 1 1, piMat 1 2 1, piMat 0 1 5, aMat,
      Matrix.diagonal fun j => if j = 3 then -1 else 1] i := fun i => by
    rw [ht, hSG, toM_map_toN _ (by simp [en4S, n4S]), en4S_getD]
  have hrefl : IsReflMat (t 0).1 :=
    isRefl_pi _ (by rw [← vmul, htt, vone]) (by rw [hmat]; rfl)
  have hord : orderOf (t 0 * t 2) = 4 := orderOf_mul_gen (by rw [hmat]; rfl) (by rw [hmat]; rfl)
  have h46080 : 46080 ≤ Nat.card (glClosure en4Gens) := by
    rw [CFSG.KD.NFMK.en4_lens] at hcard
    exact hcard
  exact ⟨t, hmat, htop, h46080, hnorm, hcen, hpair, hforms, hrefl, hord⟩

end CFSG.StandardType.ZS.NFMK

end
