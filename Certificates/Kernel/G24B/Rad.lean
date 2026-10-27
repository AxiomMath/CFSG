module

public import Certificates.Kernel.G24B.Frames
public import Certificates.Kernel.G24B.Checks733010
public import CFSG.Quasithin.Recognition.St84.G24RadFacts

public section

noncomputable section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.Fischer CFSG.Quasithin.F112R.St84.G24M CFSG.KC.Misc.Spec CFSG.KC.F2BfsRec
open CFSG.KC.Misc.G24 (mulF2 oneF2 nthV)

open scoped commutatorElement


theorem blt_lt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by simpa [Nat.blt_eq] using h

theorem orB_iff {a b : Bool} : CFSG.KLie.CT.orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> simp [CFSG.KLie.CT.orB]

theorem commute_of_commK (hC : ChevFacts) {x z : Y} {X Z : ℕ} (hx : psi x = pkMat 28 X)
    (hz : psi z = pkMat 28 Z) (h : commK X Z = true) : x * z = z * x :=
  psi_injective hC (by rw [map_mul, map_mul, hx, hz, ← pkMat_mulF2, ← pkMat_mulF2, beq_iff'.mp h])

theorem commK_of_commute (hC : ChevFacts) {x z : Y} {X Z : ℕ} (hx : psi x = pkMat 28 X)
    (hz : psi z = pkMat 28 Z) (h : x * z = z * x) : commK X Z = true := by
  have e : pkMat 28 (mulF2 28 X Z) = pkMat 28 (mulF2 28 Z X) := by
    rw [pkMat_mulF2, pkMat_mulF2, ← hx, ← hz, ← map_mul, ← map_mul, h]
  exact beq_iff'.mpr (eq_of_pk (mulF2_lt' _ _) (mulF2_lt' _ _) e)

theorem r10GoK_spec {EQ EZ : ℕ → ℕ} {GQ : List ℕ} {ngz nZ : ℕ} :
    ∀ (ws : List (ℕ × (ℕ × ℕ))) (s0 : ℕ), r10GoK EQ EZ GQ ngz nZ ws s0 = true →
      ∀ i < ws.length, r10StepK EQ EZ GQ ngz nZ (s0 + i) (ws.getD i (0, (0, 0))) = true
  | [], _, _ => fun i hi => absurd hi (Nat.not_lt_zero i)
  | d :: ws, s0, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro i hi
    rcases i with _ | i
    · exact h1
    · have e := r10GoK_spec ws (s0 + 1) h2 i (by simpa using hi)
      rw [show s0 + (i + 1) = s0 + 1 + i by omega]
      exact e

structure R10Parts (EQ EZ : ℕ → ℕ) (GQ : List ℕ) (k ngz nZ : ℕ) (ws : List (ℕ × (ℕ × ℕ)))
    (cm : List ℕ) : Prop where
  len : ws.length = 1024
  cen : ∀ t < ngz, ∀ m < 10, commK (nthV GQ (k + t)) (nthV GQ m) = true
  sqZ : ∀ s < nZ, mulF2 28 (sortedAt 28 12 6 ngz EZ s) (sortedAt 28 12 6 ngz EZ s) = oneF2 28
  cm : ∀ m < 10, ∀ m' < 10, nthV cm (10 * m + m') < nZ ∧
    mulF2 28 (nthV GQ m) (nthV GQ m') =
      mulF2 28 (sortedAt 28 12 6 ngz EZ (nthV cm (10 * m + m'))) (mulF2 28 (nthV GQ m') (nthV GQ m))
  step : ∀ s < 1024, r10StepK EQ EZ GQ ngz nZ s (ws.getD s (0, (0, 0))) = true

theorem r10K_parts {EQ EZ : ℕ → ℕ} {GQ : List ℕ} {k ngz nZ : ℕ} {ws : List (ℕ × (ℕ × ℕ))}
    {cm : List ℕ} (h : r10K EQ EZ GQ k ngz nZ ws cm = true) : R10Parts EQ EZ GQ k ngz nZ ws cm := by
  obtain ⟨h1, h⟩ := andB_iff.mp h
  obtain ⟨h2, h⟩ := andB_iff.mp h
  obtain ⟨h3, h⟩ := andB_iff.mp h
  obtain ⟨h4, h5⟩ := andB_iff.mp h
  have hlen : ws.length = 1024 := beq_iff'.mp h1
  refine ⟨hlen, fun t ht m hm => allN_iff'.mp (allN_iff'.mp h2 t ht) m hm, fun s hs => ?_,
    fun m hm m' hm' => ?_, fun s hs => ?_⟩
  · have e := allN_iff'.mp h3 s hs
    rw [strictB_eq'] at e
    exact beq_iff'.mp e
  · have e := allN_iff'.mp (allN_iff'.mp h4 m hm) m' hm'
    rw [strictB_eq'] at e
    obtain ⟨e1, e2⟩ := andB_iff.mp e
    exact ⟨blt_lt e1, beq_iff'.mp e2⟩
  · have e := r10GoK_spec ws 0 h5 s (by omega)
    rwa [Nat.zero_add] at e

theorem rad_parts (hC : ChevFacts) {y : Fin 10 → Y} {G : List ℕ} {EQ EZ : ℕ → ℕ}
    {k ngz nZ : ℕ} {ZS : Fin ngz → Y} {ws : List (ℕ × (ℕ × ℕ))} {cm : List ℕ}
    (hG : ∀ m : Fin 10, psi (y m) = pkMat 28 (nthV G m.val))
    (rQ : RecOK y 6 EQ (genR 28 12 6 10 EQ) 1024)
    (rZ : RecOK ZS 6 EZ (genR 28 12 6 ngz EZ) nZ)
    (hk : k + ngz ≤ 10) (hZS : ∀ (t : Fin ngz) (h : k + t.val < 10), ZS t = y ⟨k + t.val, h⟩)
    (h : r10K EQ EZ G k ngz nZ ws cm = true) :
    CFSG.Quasithin.centerOf (Subgroup.closure (Set.range y)) = Subgroup.closure (Set.range ZS) ∧
      (∀ z ∈ Subgroup.closure (Set.range ZS), z ^ 2 = 1) ∧
      (∀ x ∈ Subgroup.closure (Set.range y), x ^ 2 ∈ Subgroup.closure (Set.range ZS)) ∧
      (∀ x ∈ Subgroup.closure (Set.range y), ∀ w ∈ Subgroup.closure (Set.range y),
        ⁅x, w⁆ ∈ Subgroup.closure (Set.range ZS)) := by
  have P := r10K_parts h
  set Q := Subgroup.closure (Set.range y)
  set R := Subgroup.closure (Set.range ZS)
  have hsorted : ∀ x ∈ Q, ∃ s < 1024, psi x = pkMat 28 (sortedAt 28 12 6 10 EQ s) := by
    intro x hx
    obtain ⟨t, ht, he⟩ := exists_entry_of_recOK rQ hx
    obtain ⟨s, hs, e⟩ := exists_sorted_of_entry rQ.h ht
    exact ⟨s, hs, he.trans (by rw [e])⟩
  have hZsorted : ∀ z ∈ R, ∃ s < nZ, psi z = pkMat 28 (sortedAt 28 12 6 ngz EZ s) := by
    intro z hz
    obtain ⟨t, ht, he⟩ := exists_entry_of_recOK rZ hz
    obtain ⟨s, hs, e⟩ := exists_sorted_of_entry rZ.h ht
    exact ⟨s, hs, he.trans (by rw [e])⟩
  have hRQ : R ≤ Q := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    rw [hZS t (by omega)]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  have hRC : R ≤ Subgroup.centralizer (Q : Set Y) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    rw [SetLike.mem_coe, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro _ ⟨m, rfl⟩
    have ht : k + t.val < 10 := by omega
    rw [hZS t ht]
    exact (commute_of_commK hC (hG ⟨k + t.val, ht⟩) (hG m) (P.cen t.val t.2 m.val m.2)).symm
  refine ⟨le_antisymm ?_ (le_inf hRQ hRC), ?_, ?_, ?_⟩
  · rintro x ⟨hxQ, hxC⟩
    obtain ⟨s, hs, hx⟩ := hsorted x hxQ
    have e := P.step s hs
    unfold r10StepK at e
    rw [strictB_eq'] at e
    obtain ⟨e1, -⟩ := andB_iff.mp e
    rcases orB_iff.mp e1 with e1 | e1
    · obtain ⟨ew, enc⟩ := andB_iff.mp e1
      have hw : (ws.getD s (0, (0, 0))).1 < 10 := blt_lt ew
      have hc := commK_of_commute hC hx (hG ⟨_, hw⟩)
        (Subgroup.mem_centralizer_iff.mp hxC _ (Subgroup.subset_closure ⟨_, rfl⟩)).symm
      rw [notB_iff] at enc
      rw [hc] at enc
      exact absurd enc (by decide)
    · obtain ⟨ep, ex⟩ := andB_iff.mp e1
      have hp : (ws.getD s (0, (0, 0))).2.1 < nZ := by simpa [Nat.blt_eq] using ep
      exact mem_of_sorted hC rZ hp (hx.trans (by rw [beq_iff'.mp ex]))
  · intro z hz
    obtain ⟨s, hs, he⟩ := hZsorted z hz
    refine psi_injective hC ?_
    rw [pow_two, map_mul, he, map_one, ← pkMat_mulF2, P.sqZ s hs, pkMat_oneF2]
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := hsorted x hx
    have e := P.step s hs
    unfold r10StepK at e
    rw [strictB_eq'] at e
    obtain ⟨-, e2⟩ := andB_iff.mp e
    obtain ⟨eq, ex⟩ := andB_iff.mp e2
    have hq : (ws.getD s (0, (0, 0))).2.2 < nZ := by simpa [Nat.blt_eq] using eq
    refine mem_of_sorted hC rZ hq ?_
    rw [pow_two, map_mul, hxs, ← pkMat_mulF2, beq_iff'.mp ex]
  · intro x hx w hw
    refine CFSG.LocalAnalysis.ComponentInitial.LinearCover.commutatorElement_mem_of_mem_closure
      (fun g hg r hr => ?_) ?_ hx hw
    · rw [Subgroup.mem_centralizer_iff.mp (hRC hr) g hg, mul_inv_cancel_right]
      exact hr
    · rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩
      obtain ⟨hc, he⟩ := P.cm m.val m.2 m'.val m'.2
      obtain ⟨z, hz, hzs⟩ := exists_mem_of_sorted rZ hc
      have hm : y m * y m' = z * (y m' * y m) := psi_injective hC (by
        rw [map_mul, map_mul, map_mul, hG, hG, hzs, ← pkMat_mulF2, ← pkMat_mulF2,
          ← pkMat_mulF2, he])
      have : ⁅y m, y m'⁆ = z := by
        rw [commutatorElement_def, hm]
        group
      rw [this]
      exact hz

theorem psi_signedProd {m : ℕ} {x : Fin m → Y} {G Gi : ℕ → ℕ}
    (hG : ∀ i : Fin m, psi (x i) = pkMat 28 (G i.val))
    (hGi : ∀ i : Fin m, psi (x i)⁻¹ = pkMat 28 (Gi i.val)) :
    ∀ w : List (Fin m × Bool), psi (CFSG.Certificates.signedProd x w) = pkMat 28 (r10SgK G Gi w)
  | [] => by
    change psi (CFSG.Certificates.signedProd x []) = pkMat 28 (oneF2 28)
    rw [CFSG.Certificates.signedProd_nil, map_one, pkMat_oneF2]
  | l :: w => by
    change _ = pkMat 28 (mulF2 28 (Bool.rec (motive := fun _ => ℕ) (Gi l.1.val) (G l.1.val) l.2)
      (r10SgK G Gi w))
    rw [CFSG.Certificates.signedProd_cons, map_mul, psi_signedProd hG hGi w, pkMat_mulF2]
    obtain ⟨i, b⟩ := l
    cases b
    · rw [if_neg Bool.false_ne_true, hGi i]
    · rw [if_pos rfl, hG i]

theorem r10RelsK_spec {m : ℕ} {G Gi : ℕ → ℕ} :
    ∀ {rels : List (List (Fin m × Bool))}, r10RelsK G Gi rels = true →
      ∀ r ∈ rels, r10SgK G Gi r = oneF2 28
  | [], _ => by simp
  | r :: rels, h => by
    obtain ⟨h1, h2⟩ := andB_iff.mp h
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr'
    · exact beq_iff'.mp h1
    · exact r10RelsK_spec h2 r' hr'

theorem rels_of_check (hC : ChevFacts) {m : ℕ} {x : Fin m → Y} {G Gi : ℕ → ℕ}
    (hG : ∀ i : Fin m, psi (x i) = pkMat 28 (G i.val))
    (hGi : ∀ i : Fin m, psi (x i)⁻¹ = pkMat 28 (Gi i.val)) {rels : List (List (Fin m × Bool))}
    (h : r10RelsK G Gi rels = true) : ∀ w ∈ rels, CFSG.Certificates.signedProd x w = 1 := by
  intro w hw
  refine psi_injective hC ?_
  rw [psi_signedProd hG hGi w, r10RelsK_spec h w hw, pkMat_oneF2, map_one]

theorem rels_sub (hC : ChevFacts) {m : ℕ} {K : Subgroup Y} {x : Fin m → ↥K} {G Gi : ℕ → ℕ}
    (hG : ∀ i : Fin m, psi (x i : Y) = pkMat 28 (G i.val))
    (hGi : ∀ i : Fin m, psi (x i : Y)⁻¹ = pkMat 28 (Gi i.val)) {rels : List (List (Fin m × Bool))}
    (h : r10RelsK G Gi rels = true) : ∀ w ∈ rels, CFSG.Certificates.signedProd x w = 1 := by
  intro w hw
  refine Subtype.ext ?_
  have e := CFSG.Certificates.map_signedProd K.subtype x w
  rw [Subgroup.coe_subtype] at e
  rw [OneMemClass.coe_one]
  exact e.trans (rels_of_check hC hG hGi h w hw)

theorem psi_inv_of (hC : ChevFacts) {x : Y} {X P : ℕ} (hx : psi x = pkMat 28 X)
    (h : mulF2 28 P X = oneF2 28) : psi x⁻¹ = pkMat 28 P := by
  have h1 : pkMat 28 P * psi x = 1 := by rw [hx, ← pkMat_mulF2, h, pkMat_oneF2]
  calc psi x⁻¹ = (pkMat 28 P * psi x) * psi x⁻¹ := by rw [h1, one_mul]
    _ = pkMat 28 P := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem psi_inv_gen (hC : ChevFacts) {n : ℕ} {x : Fin n → Y} {G es : List ℕ}
    (hG : ∀ i : Fin n, psi (x i) = pkMat 28 (nthV G i.val)) (h : r10InvOK G es n = true)
    (i : Fin n) : psi (x i)⁻¹ = pkMat 28 (r10InvK G es i.val) :=
  psi_inv_of hC (hG i) (beq_iff'.mp (allN_iff'.mp h i.val i.2))

@[expose] def zs1 : Fin 2 → Y := ![pc1Y 8, pc1Y 9]

@[expose] def zs2 : Fin 4 → Y := ![pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9]

theorem range_zs1 : Set.range zs1 = ({pc1Y 8, pc1Y 9} : Set Y) := by
  rw [zs1, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union]

theorem range_zs2 : Set.range zs2 = ({pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9} : Set Y) := by
  rw [zs2, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.singleton_union, Set.singleton_union,
    Set.singleton_union]

theorem rZ1 (hC : ChevFacts) : RecOK zs1 6 EZ1.CF (genR 28 12 6 2 EZ1.CF) 4 :=
  recOK_of hC (ws := wZ1) (fun j => by fin_cases j <;> rfl) ch733010_z1Pins (by norm_num)
    (by norm_num) ch733010_z1Head ch733010_z1Recs

theorem rZ2 (hC : ChevFacts) : RecOK zs2 6 EZ2.CF (genR 28 12 6 4 EZ2.CF) 16 :=
  recOK_of hC (ws := wZ2) (fun j => by fin_cases j <;> rfl) ch733010_z2Pins (by norm_num)
    (by norm_num) ch733010_z2Head ch733010_z2Recs


theorem psi_A1img (hC : ChevFacts) (i : Fin 3) :
    psi (A1imgQ i : Y) = pkMat 28 (r10ImgK (nthV GA1) (r10InvK GA1 r10EA) i.val) ∧
      psi (A1imgQ i : Y)⁻¹ = pkMat 28 (r10ImgK (r10InvK GA1 r10EA) (nthV GA1) i.val) := by
  have hi := psi_inv_gen hC (psi_A1gen hC) ch733010_invA1
  fin_cases i
  · exact ⟨psi_A1gen hC 0, hi 0⟩
  · refine ⟨hi 1, ?_⟩
    change psi (A1gen 1)⁻¹⁻¹ = _
    rw [inv_inv]
    exact psi_A1gen hC 1
  · refine ⟨hi 2, ?_⟩
    change psi (A1gen 2)⁻¹⁻¹ = _
    rw [inv_inv]
    exact psi_A1gen hC 2

theorem psi_A2img (hC : ChevFacts) (i : Fin 3) :
    psi (A2imgQ i : Y) = pkMat 28 (r10ImgK (nthV GA2) (r10InvK GA2 r10EA) i.val) ∧
      psi (A2imgQ i : Y)⁻¹ = pkMat 28 (r10ImgK (r10InvK GA2 r10EA) (nthV GA2) i.val) := by
  have hi := psi_inv_gen hC (psi_A2gen hC) ch733010_invA2
  fin_cases i
  · exact ⟨psi_A2gen hC 0, hi 0⟩
  · refine ⟨hi 1, ?_⟩
    change psi (A2gen 1)⁻¹⁻¹ = _
    rw [inv_inv]
    exact psi_A2gen hC 1
  · refine ⟨hi 2, ?_⟩
    change psi (A2gen 2)⁻¹⁻¹ = _
    rw [inv_inv]
    exact psi_A2gen hC 2

theorem radFacts (hC : ChevFacts) : RadFacts := by
  obtain ⟨z1, sz1, sq1, cm1⟩ := rad_parts hC (psi_pc1 hC) (rQ1 hC) (rZ1 hC) (k := 8)
    (by norm_num) (fun t _ => by fin_cases t <;> rfl) ch733010_rad1
  obtain ⟨z2, sz2, sq2, cm2⟩ := rad_parts hC (psi_pc2 hC) (rQ2 hC) (rZ2 hC) (k := 6)
    (by norm_num) (fun t _ => by fin_cases t <;> rfl) ch733010_rad2
  have h1 : Z1 = Subgroup.closure (Set.range zs1) := z1
  have h2 : Z2 = Subgroup.closure (Set.range zs2) := z2
  have e1 : Z1 = Subgroup.closure {pc1Y 8, pc1Y 9} := by rw [← range_zs1]; exact z1
  have e2 : Z2 = Subgroup.closure {pc2Y 6, pc2Y 7, pc2Y 8, pc2Y 9} := by
    rw [← range_zs2]; exact z2
  refine ⟨e1, ?_, fun z hz => sz1 z (by rw [← h1]; exact hz), fun x hx => by rw [h1]; exact sq1 x hx,
    fun x hx w hw => by rw [h1]; exact cm1 x hx w hw, e2, ?_,
    fun z hz => sz2 z (by rw [← h2]; exact hz), fun x hx => by rw [h2]; exact sq2 x hx,
    fun x hx w hw => by rw [h2]; exact cm2 x hx w hw, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    exact card_of_recOK hC (rZ1 hC)
  · rw [h2]
    exact card_of_recOK hC (rZ2 hC)
  · intro heq
    have hX : nthV GQ1 3 < 2 ^ (28 * 28) := by
      rw [nthV_eq, GQ1, getD_map_lt (by rw [show wQ1.length = 10 from rfl]; omega) 0 []]
      exact wordF4_lt _ _
    refine not_mem_of_gap (rQ2 hC) hX (psi_pc1 hC 3) ch733010_gap12 ?_
    have hm : pc1Y 3 ∈ Q1 := Subgroup.subset_closure ⟨3, rfl⟩
    rw [heq] at hm
    exact hm
  · exact rels_sub hC (K := Q1) (x := pc1Q) (G := nthV GQ1) (Gi := r10InvK GQ1 r10EQ)
      (fun i => psi_pc1 hC i) (psi_inv_gen hC (psi_pc1 hC) ch733010_invQ1) ch733010_relsQ1
  · exact rels_sub hC (K := Q2) (x := pc2Q) (G := nthV GQ2) (Gi := r10InvK GQ2 r10EQ)
      (fun i => psi_pc2 hC i) (psi_inv_gen hC (psi_pc2 hC) ch733010_invQ2) ch733010_relsQ2
  · exact rels_sub hC (K := A1) (x := A1Q) (G := nthV GA1) (Gi := r10InvK GA1 r10EA)
      (fun i => psi_A1gen hC i) (psi_inv_gen hC (psi_A1gen hC) ch733010_invA1) ch733010_relsA1
  · exact rels_sub hC (K := A2) (x := A2Q) (G := nthV GA2) (Gi := r10InvK GA2 r10EA)
      (fun i => psi_A2gen hC i) (psi_inv_gen hC (psi_A2gen hC) ch733010_invA2) ch733010_relsA2
  · exact rels_sub hC (K := A1) (x := A1imgQ) (G := r10ImgK (nthV GA1) (r10InvK GA1 r10EA))
      (Gi := r10ImgK (r10InvK GA1 r10EA) (nthV GA1))
      (fun i => (psi_A1img hC i).1) (fun i => (psi_A1img hC i).2) ch733010_relsA1img
  · exact rels_sub hC (K := A2) (x := A2imgQ) (G := r10ImgK (nthV GA2) (r10InvK GA2 r10EA))
      (Gi := r10ImgK (r10InvK GA2 r10EA) (nthV GA2))
      (fun i => (psi_A2img hC i).1) (fun i => (psi_A2img hC i).2) ch733010_relsA2img

end CFSG.KD.G24B
