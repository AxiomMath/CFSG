module

public import Certificates.Kernel.Fi24.Top
public import CFSG.Sporadic.Presentation.Fi24PrimeExactInputs
public import CFSG.Certificates.Kernel.Orders.Fi24p.RelsBind
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P1_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P2_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P3_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P4_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P5_Sel
public import CFSG.Certificates.Kernel.Fi24.PG10.Data.P6_Sel
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelPG10

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CertificateChecks.KernelCo2
  CertificateChecks.KernelFi24 CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime

abbrev S0 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]

abbrev m0 : ℕ := TauCeti.SporadicName.Fi24Prime.presentation.generatorCount

abbrev n10 : ℕ := (subsetOf m0 S0).length

abbrev rels10 : Set (FreeGroup (Fin n10)) := {r | r ∈ X1.map FreeGroup.mk}

abbrev G10 : Type := PG n10 X1

@[expose] def toNw {n : ℕ} (w : List (Fin n × Bool)) : List (ℕ × Bool) := w.map fun l => (l.1.val, l.2)

@[expose] def ofNw (w : List (ℕ × Bool)) : List (Fin 11 × Bool) := w.map fun l => (Fin.ofNat 11 l.1, l.2)

@[expose] def entW {n : ℕ} (w : List (Fin n × Bool)) : ℕ := Co2B.ent (toNw w)

@[expose] def A1 : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
@[expose] def A2 : List ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 9]
@[expose] def A3 : List ℕ := [0, 1, 2, 3, 4, 6, 8, 9]
@[expose] def A4 : List ℕ := [0, 1, 2, 3, 4, 6, 9]
@[expose] def A5 : List ℕ := [0, 1, 2, 3, 4, 6]
@[expose] def A6 : List ℕ := [0, 1, 2, 3, 4]

@[expose] def U1 : List ℕ := [0, 1, 2, 3, 4, 6, 7, 8, 9]
@[expose] def U2 : List ℕ := [0, 1, 2, 3, 4, 5, 7, 8]
@[expose] def U3 : List ℕ := [0, 1, 2, 3, 4, 5, 7]
@[expose] def U4 : List ℕ := [0, 1, 2, 3, 4, 5]
@[expose] def U5 : List ℕ := [0, 1, 2, 3, 4]

theorem m0_eq : m0 = 11 := by
  change TauCeti.Sporadic.fi24PrimePresentation.generatorNames.length = 11
  rw [TauCeti.Sporadic.fi24PrimePresentation_generatorNames]
  rfl

theorem x0_letters : X0.map toNw = CFSG.KD.OrdFi24p.rels := by
  have h := CFSG.KD.OrdFi24p.rels_eq
  rw [TauCeti.GroupPresentation.relatorLetters_def] at h
  exact h

theorem ws_eq (ws : List (List (Fin 11 × Bool))) (h : ws.map toNw = CFSG.KD.OrdFi24p.rels) :
    ws = CFSG.KD.OrdFi24p.rels.map ofNw := by
  rw [← h, List.map_map]
  conv_lhs => rw [← List.map_id ws]
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply, id, ofNw, toNw, List.map_map]
  conv_lhs => rw [← List.map_id w]
  apply List.map_congr_left
  intro l _
  exact Prod.ext (Fin.ext (by simp)) rfl

abbrev Form {m : ℕ} (ws : List (List (Fin m × Bool))) (A : List ℕ) (RT : ℕ → ℕ) (R : ℕ) : Prop :=
  (subsetOf (subsetOf m S0).length A).map Fin.val = A ∧
    (∀ w ∈ restrictWords (subsetOf (subsetOf m S0).length A) (restrictWords (subsetOf m S0) ws),
      w.length < 1024) ∧
    (restrictWords (subsetOf (subsetOf m S0).length A) (restrictWords (subsetOf m S0) ws)).map entW =
      (List.range R).map RT

theorem form1 {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) : Form ws A1 CFSG.KD.PG10P1.selRT 112 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem form2 {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) : Form ws A2 CFSG.KD.PG10P2.selRT 92 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem form3 {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) : Form ws A3 CFSG.KD.PG10P3.selRT 74 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem form4 {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) : Form ws A4 CFSG.KD.PG10P4.selRT 58 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem form5 {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) : Form ws A5 CFSG.KD.PG10P5.selRT 42 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem form6 {m : ℕ} (hm : m = 11) {ws : List (List (Fin m × Bool))}
    (hws : ws.map toNw = CFSG.KD.OrdFi24p.rels) : Form ws A6 CFSG.KD.PG10P6.selRT 30 := by
  subst hm
  rw [ws_eq ws hws]
  decide +kernel

theorem n10_eq : n10 = 10 := by
  change (subsetOf m0 S0).length = 10
  rw [m0_eq]
  rfl

noncomputable abbrev gen (A : List ℕ) : ℕ → G10 := fun j => pgen rels10 (A.getD j 0)

theorem swd_restrict {n : ℕ} (X : List (List (Fin n × Bool))) (S : List (Fin n))
    {w' : List (Fin S.length × Bool)} (hw : w' ∈ restrictWords S X) :
    swd (fun j => pgen {r : FreeGroup (Fin n) | r ∈ X.map FreeGroup.mk} ((S.map Fin.val).getD j 0))
      (toNw w') = 1 := by
  obtain ⟨w, hwX, hren⟩ := List.mem_filterMap.mp hw
  have hm := map_renumber S w w' hren
  have hg : ∀ j : Fin S.length, (S.map Fin.val).getD j.val 0 = (S.get j).val := by
    intro j
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  have e : swd (fun j => pgen {r : FreeGroup (Fin n) | r ∈ X.map FreeGroup.mk} ((S.map Fin.val).getD j 0))
      (toNw w') = swd (pgen {r : FreeGroup (Fin n) | r ∈ X.map FreeGroup.mk}) (toNw w) := by
    unfold swd toNw
    rw [← hm, List.map_map, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro l _
    simp only [Function.comp_apply, hg]
  rw [e]
  change swd _ (w.map fun l => (l.1.val, l.2)) = 1
  rw [swd_pgen']
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hwX)

theorem rels_val {A : List ℕ} {RT : ℕ → ℕ} {R : ℕ} (h : Form X0 A RT R) (hA : A.length ≤ 127) :
    ∀ r < R, bval (gen A) (wWord (RT r)) (wLen (RT r)) = 1 := by
  obtain ⟨hS, hlen, hrel⟩ := h
  change (subsetOf n10 A).map Fin.val = A at hS
  change ∀ w ∈ restrictWords (subsetOf n10 A) X1, w.length < 1024 at hlen
  change (restrictWords (subsetOf n10 A) X1).map entW = (List.range R).map RT at hrel
  generalize hL : restrictWords (subsetOf n10 A) X1 = L at hlen hrel
  intro r hr
  have hl : L.length = R := by
    have := congrArg List.length hrel
    rwa [List.length_map, List.length_map, List.length_range] at this
  have hrL : r < L.length := by omega
  have e : entW L[r] = RT r := by
    have := List.getElem_of_eq hrel (by rw [List.length_map]; exact hrL)
    rwa [List.getElem_map, List.getElem_map, List.getElem_range] at this
  have hmem : L[r] ∈ restrictWords (subsetOf n10 A) X1 := by
    rw [hL]
    exact List.getElem_mem hrL
  rw [← e]
  unfold entW
  have hSl : (subsetOf n10 A).length ≤ 127 := by
    rw [← List.length_map Fin.val, hS]
    exact hA
  rw [bval_ent _ _ ?_ ?_]
  · have := swd_restrict X1 (subsetOf n10 A) hmem
    rw [hS] at this
    exact this
  · intro l hl'
    obtain ⟨⟨j, b⟩, -, rfl⟩ := List.mem_map.mp hl'
    exact lt_of_lt_of_le j.isLt (by omega)
  · rw [toNw, List.length_map]
    exact hlen _ (List.getElem_mem hrL)

theorem r1 : ∀ r < 112, bval (gen A1) (wWord (CFSG.KD.PG10P1.selRT r)) (wLen (CFSG.KD.PG10P1.selRT r)) = 1 :=
  rels_val (form1 m0_eq x0_letters) (by decide)

theorem r2 : ∀ r < 92, bval (gen A2) (wWord (CFSG.KD.PG10P2.selRT r)) (wLen (CFSG.KD.PG10P2.selRT r)) = 1 :=
  rels_val (form2 m0_eq x0_letters) (by decide)

theorem r3 : ∀ r < 74, bval (gen A3) (wWord (CFSG.KD.PG10P3.selRT r)) (wLen (CFSG.KD.PG10P3.selRT r)) = 1 :=
  rels_val (form3 m0_eq x0_letters) (by decide)

theorem r4 : ∀ r < 58, bval (gen A4) (wWord (CFSG.KD.PG10P4.selRT r)) (wLen (CFSG.KD.PG10P4.selRT r)) = 1 :=
  rels_val (form4 m0_eq x0_letters) (by decide)

theorem r5 : ∀ r < 42, bval (gen A5) (wWord (CFSG.KD.PG10P5.selRT r)) (wLen (CFSG.KD.PG10P5.selRT r)) = 1 :=
  rels_val (form5 m0_eq x0_letters) (by decide)

theorem r6 : ∀ r < 30, bval (gen A6) (wWord (CFSG.KD.PG10P6.selRT r)) (wLen (CFSG.KD.PG10P6.selRT r)) = 1 :=
  rels_val (form6 m0_eq x0_letters) (by decide)

theorem bval_single {G : Type*} [Group G] (g : ℕ → G) {e c : ℕ} (hl : wLen e = 1)
    (hw : wWord e = 2 * c) (hc : c < 128) : bval g (wWord e) (wLen e) = g c := by
  have e1 : 2 * c / 2 ^ (8 * 0) % 256 = 2 * c := by
    rw [Nat.mul_zero, pow_zero, Nat.div_one]
    omega
  rw [hl, hw, bval_succ, show bval g (2 * c / 256) 0 = 1 from rfl, mul_one, wLet_eq, e1]
  unfold letV
  have e2 : ¬ 2 * c = 255 := by omega
  have e3 : 2 * c % 2 = 0 := by omega
  have e4 : 2 * c / 2 = c := by omega
  simp only [e2, e3, e4, ↓reduceIte]

abbrev SubForm (ST : ℕ → ℕ) (K : ℕ) (A U B : List ℕ) : Prop :=
  ∀ j < K, wLen (ST j) = 1 ∧ wWord (ST j) = 2 * U.getD j 0 ∧ U.getD j 0 < 128 ∧
    A.getD (U.getD j 0) 0 = B.getD j 0

theorem sub_img {ST : ℕ → ℕ} {K L : ℕ} {A U B : List ℕ} (h : SubForm ST K A U B) (hL : 2 * K = L) :
    (fun j => bval (gen A) (wWord (ST j)) (wLen (ST j))) '' {j | j < K} = gen B '' {g | 2 * g < L} := by
  have e : {g : ℕ | 2 * g < L} = {j | j < K} := by
    ext g
    simp only [Set.mem_ofPred_eq]
    omega
  rw [e]
  apply Set.image_congr
  intro j hj
  obtain ⟨h1, h2, h3, h4⟩ := h j hj
  rw [bval_single _ h1 h2 h3]
  change pgen rels10 (A.getD (U.getD j 0) 0) = pgen rels10 (B.getD j 0)
  rw [h4]

theorem sub1 : SubForm CFSG.KD.PG10P1.selST (nat_lit 9) A1 U1 A2 := by decide +kernel
theorem sub2 : SubForm CFSG.KD.PG10P2.selST (nat_lit 8) A2 U2 A3 := by decide +kernel
theorem sub3 : SubForm CFSG.KD.PG10P3.selST (nat_lit 7) A3 U3 A4 := by decide +kernel
theorem sub4 : SubForm CFSG.KD.PG10P4.selST (nat_lit 6) A4 U4 A5 := by decide +kernel
theorem sub5 : SubForm CFSG.KD.PG10P5.selST (nat_lit 5) A5 U5 A6 := by decide +kernel

theorem closure_gen1 : Subgroup.closure (gen A1 '' {g | 2 * g < nat_lit 20}) = ⊤ := by
  rw [← closure_pgen rels10]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, by rw [n10_eq]; change 2 * g < 20 at hg; omega, ?_⟩
    change pgen rels10 g = pgen rels10 (A1.getD g 0)
    congr 1
    change 2 * g < 20 at hg
    have hg' : g < 10 := by omega
    interval_cases g <;> rfl
  · rintro ⟨g, hg, rfl⟩
    rw [n10_eq] at hg
    refine ⟨g, by omega, ?_⟩
    change pgen rels10 (A1.getD g 0) = pgen rels10 g
    congr 1
    interval_cases g <;> rfl

end CertificateChecks.KernelPG10

end
