module

public import CFSG.GH74.E2.L33OuterTablesInputs
public import Certificates.Data.Kernel.Census.CatFacts.PkDefs
import CFSG.Certificates.Kernel.Census.CatFacts.PkEnum

public section

set_option maxHeartbeats 0
set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSchreierFam

open CFSG.GH74.E2 CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkEnum CFSG.Certificates CFSG.KS.PK
  CFSG.Sporadic.Schreier

variable {n : ℕ}

@[expose] def repComm (QP : RawSchreierDatum n) (τ a b : Equiv.Perm (Fin n)) : Bool :=
  isOuterInv QP τ && decide (a * τ = τ * a) && decide (b * τ = τ * b) &&
    decide ((a * b * a⁻¹ * b⁻¹) ^ 2 = 1) && !decide (a * b * a⁻¹ * b⁻¹ = 1)

@[expose] def repCommAt (QP : RawSchreierDatum n) (LA LP : List (Equiv.Perm (Fin n)))
    (i j k : ℕ) : Bool :=
  match (LA.drop i).head?, (LP.drop j).head?, (LP.drop k).head? with
  | some τ, some a, some b => repComm QP τ a b
  | _, _, _ => false

@[expose] def conjAtIdx (L : List (Equiv.Perm (Fin n))) (τ0 τ : Equiv.Perm (Fin n)) (w : ℕ) :
    Bool :=
  match (L.drop w).head? with
  | some σ => decide (σ * τ0 * σ⁻¹ = τ)
  | none => false

@[expose] def conjWalk (QP : RawSchreierDatum n) (L : List (Equiv.Perm (Fin n)))
    (τ0 : Equiv.Perm (Fin n)) : List (Equiv.Perm (Fin n)) → List ℕ → Bool
  | [], _ => true
  | τ :: rest, ws => if isOuterInv QP τ then
      (match ws with
        | w :: ws' => conjAtIdx L τ0 τ w && conjWalk QP L τ0 rest ws'
        | [] => false)
    else conjWalk QP L τ0 rest ws

@[expose] def conjRepAt (QP : RawSchreierDatum n) (L : List (Equiv.Perm (Fin n))) (i : ℕ)
    (ws : List ℕ) : Bool :=
  match (L.drop i).head? with
  | some τ0 => isOuterInv QP τ0 && conjWalk QP L τ0 L ws
  | none => false

theorem mem_of_head?_drop {L : List (Equiv.Perm (Fin n))} {i : ℕ} {x : Equiv.Perm (Fin n)}
    (h : (L.drop i).head? = some x) : x ∈ L :=
  List.mem_of_mem_drop (List.mem_of_mem_head? h)

theorem repCommAt_spec {QP : RawSchreierDatum n} {LA LP : List (Equiv.Perm (Fin n))}
    {i j k : ℕ} (h : repCommAt QP LA LP i j k = true) :
    ∃ τ a b, (LA.drop i).head? = some τ ∧ (LP.drop j).head? = some a ∧
      (LP.drop k).head? = some b ∧ repComm QP τ a b = true := by
  unfold repCommAt at h
  split at h
  · next τ a b h1 h2 h3 => exact ⟨τ, a, b, h1, h2, h3, h⟩
  · exact absurd h Bool.false_ne_true

theorem conjWalk_spec (QP : RawSchreierDatum n) (L : List (Equiv.Perm (Fin n)))
    (τ0 : Equiv.Perm (Fin n)) :
    ∀ (M : List (Equiv.Perm (Fin n))) (ws : List ℕ), conjWalk QP L τ0 M ws = true →
      ∀ τ ∈ M, isOuterInv QP τ = true → ∃ σ ∈ L, σ * τ0 * σ⁻¹ = τ
  | [], _, _, τ, hτ, _ => absurd hτ List.not_mem_nil
  | τ' :: rest, ws, h, τ, hτ, ho => by
    unfold conjWalk at h
    by_cases ho' : isOuterInv QP τ' = true
    · rw [if_pos ho'] at h
      cases ws with
      | nil => exact absurd h Bool.false_ne_true
      | cons w ws' =>
        rw [Bool.and_eq_true] at h
        rcases List.mem_cons.1 hτ with rfl | hτ
        · have h1 := h.1
          unfold conjAtIdx at h1
          split at h1
          · next σ hσ => exact ⟨σ, mem_of_head?_drop hσ, of_decide_eq_true h1⟩
          · exact absurd h1 Bool.false_ne_true
        · exact conjWalk_spec QP L τ0 rest ws' h.2 τ hτ ho
    · rw [if_neg ho'] at h
      rcases List.mem_cons.1 hτ with rfl | hτ
      · exact absurd ho ho'
      · exact conjWalk_spec QP L τ0 rest ws h τ hτ ho

theorem outerConjCheck_of_rep {QP : RawSchreierDatum n} {L : List (Equiv.Perm (Fin n))} {i : ℕ}
    {ws : List ℕ} (h : conjRepAt QP L i ws = true) : outerConjCheck QP L = true := by
  unfold conjRepAt at h
  split at h
  · next τ0 hτ0 =>
    rw [Bool.and_eq_true] at h
    refine List.any_eq_true.2 ⟨τ0, mem_of_head?_drop hτ0, ?_⟩
    rw [outerConjAt, Bool.and_eq_true]
    refine ⟨h.1, List.all_eq_true.2 fun τ hτ => ?_⟩
    rw [Bool.or_eq_true]
    by_cases ho : isOuterInv QP τ = true
    · right
      obtain ⟨σ, hσ, e⟩ := conjWalk_spec QP L τ0 L ws h.2 τ hτ ho
      exact List.any_eq_true.2 ⟨σ, hσ, decide_eq_true e⟩
    · left
      simp [ho]
  · exact absurd h Bool.false_ne_true

theorem conj_mem_of_normCheck (QP QA : RawSchreierDatum n) (hQP : ValidSchreier QP)
    {gA gB : Equiv.Perm (Fin n)} (hP : QP.originalSubgroup = Subgroup.closure {gA, gB})
    (hnorm : normCheck QP QA.original.toList gA gB = true) {σ x : Equiv.Perm (Fin n)}
    (hσ : σ ∈ QA.originalSubgroup) (hx : x ∈ QP.originalSubgroup) :
    σ * x * σ⁻¹ ∈ QP.originalSubgroup := by
  have hnormA : QA.originalSubgroup ≤
      Subgroup.normalizer (QP.originalSubgroup : Set (Equiv.Perm (Fin n))) := by
    rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro σ hσ
    have hσ' : σ ∈ QA.original.toList := hσ
    have h1 := List.all_eq_true.1 hnorm σ hσ'
    simp only [Bool.and_eq_true] at h1
    have ha : σ * gA * σ⁻¹ ∈ QP.originalSubgroup := (mem_iff_sift QP hQP _).2 h1.1
    have hb : σ * gB * σ⁻¹ ∈ QP.originalSubgroup := (mem_iff_sift QP hQP _).2 h1.2
    apply mem_normalizer_of_conj_mem
    intro x hx
    have hle : Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) ≤
        QP.originalSubgroup.comap (MulAut.conj σ).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]; exact ha
      · rw [Set.mem_singleton_iff] at hy
        rw [hy]; exact hb
    have hx' : x ∈ Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin n))) := hP ▸ hx
    exact hle hx'
  exact (Subgroup.mem_normalizer_iff.1 (hnormA hσ) x).1 hx

theorem outerCommCheck_of_rep (QP QA : RawSchreierDatum n) (hQP : ValidSchreier QP)
    (hQA : ValidSchreier QA) {gA gB : Equiv.Perm (Fin n)}
    (hP : QP.originalSubgroup = Subgroup.closure {gA, gB})
    (hnorm : normCheck QP QA.original.toList gA gB = true)
    (hconj : outerConjCheck QP (elemsT QA) = true) {i j k : ℕ}
    (hrep : repCommAt QP (elemsT QA) (elemsT QP) i j k = true) :
    outerCommCheck QP (elemsT QA) (elemsT QP) = true := by
  obtain ⟨τ1, a, b, hτ1, ha, hb, hrep⟩ := repCommAt_spec hrep
  have hτ1L := mem_of_head?_drop hτ1
  have haP := (mem_elemsT QP hQP a).1 (mem_of_head?_drop ha)
  have hbP := (mem_elemsT QP hQP b).1 (mem_of_head?_drop hb)
  simp only [repComm, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
    decide_eq_false_iff_not] at hrep
  obtain ⟨⟨⟨⟨hτ1o, hca⟩, hcb⟩, hsq⟩, hne⟩ := hrep
  obtain ⟨τ0, -, hτ0⟩ := List.any_eq_true.1 hconj
  rw [outerConjAt, Bool.and_eq_true] at hτ0
  have hconjOf : ∀ τ ∈ elemsT QA, isOuterInv QP τ = true →
      ∃ σ ∈ QA.originalSubgroup, σ * τ0 * σ⁻¹ = τ := by
    intro τ hτ ho
    have h1 := List.all_eq_true.1 hτ0.2 τ hτ
    rw [ho, Bool.not_true, Bool.false_or] at h1
    obtain ⟨σ, hσL, hσ⟩ := List.any_eq_true.1 h1
    exact ⟨σ, (mem_elemsT QA hQA σ).1 hσL, of_decide_eq_true hσ⟩
  obtain ⟨σ1, hσ1, e1⟩ := hconjOf τ1 hτ1L hτ1o
  refine List.all_eq_true.2 fun τ hτ => ?_
  rw [Bool.or_eq_true]
  by_cases ho : isOuterInv QP τ = true
  · right
    obtain ⟨σ, hσ, e⟩ := hconjOf τ hτ ho
    set g := σ * σ1⁻¹ with hg
    have hgA : g ∈ QA.originalSubgroup :=
      QA.originalSubgroup.mul_mem hσ (QA.originalSubgroup.inv_mem hσ1)
    have eτ : τ = g * τ1 * g⁻¹ := by
      rw [← e, ← e1, hg]
      group
    have hcomm : ∀ x, x * τ1 = τ1 * x → (g * x * g⁻¹) * τ = τ * (g * x * g⁻¹) := by
      intro x hx
      rw [eτ]
      calc g * x * g⁻¹ * (g * τ1 * g⁻¹) = g * (x * τ1) * g⁻¹ := by group
        _ = g * (τ1 * x) * g⁻¹ := by rw [hx]
        _ = g * τ1 * g⁻¹ * (g * x * g⁻¹) := by group
    have hcomm' : (g * a * g⁻¹) * (g * b * g⁻¹) * (g * a * g⁻¹)⁻¹ * (g * b * g⁻¹)⁻¹ =
        g * (a * b * a⁻¹ * b⁻¹) * g⁻¹ := by group
    refine List.any_eq_true.2 ⟨g * a * g⁻¹, ?_, List.any_eq_true.2 ⟨g * b * g⁻¹, ?_, ?_⟩⟩
    · exact List.mem_filter.2 ⟨(mem_elemsT QP hQP _).2
        (conj_mem_of_normCheck QP QA hQP hP hnorm hgA haP), decide_eq_true (hcomm a hca)⟩
    · exact List.mem_filter.2 ⟨(mem_elemsT QP hQP _).2
        (conj_mem_of_normCheck QP QA hQP hP hnorm hgA hbP), decide_eq_true (hcomm b hcb)⟩
    · rw [hcomm', Bool.and_eq_true]
      refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
      · rw [← MulAut.conj_apply, ← map_pow, hsq, map_one]
      · intro h1
        apply hne
        have h2 : g⁻¹ * (g * (a * b * a⁻¹ * b⁻¹) * g⁻¹) * g = g⁻¹ * 1 * g := by rw [h1]
        simpa [mul_assoc] using h2
  · left
    simp [ho]

@[expose] def conjWs : List ℕ :=
  [0, 1081, 116, 614, 469, 36, 1800, 8, 549, 183, 908, 3, 180, 108, 39, 188, 111, 44, 144, 110, 290,
  147, 758, 1452, 223, 1160, 220, 109, 297, 152, 228, 3252, 615, 117, 684, 289, 1159, 184, 367, 145,
  192, 831, 399, 396, 830, 364, 187, 153, 1153, 372, 146, 2341, 832, 404, 1880, 328, 397, 829, 835,
  405, 43, 867, 398, 828, 331, 300, 40, 336, 48, 292, 2342, 295, 865, 439, 440, 907, 655, 1192, 1262,
  1084, 873, 657, 981, 651, 1011, 434, 1092, 1261, 1224, 1124, 868, 259, 840, 408, 120, 1587, 73,
  264, 115, 836, 400, 74, 112, 256, 81, 2088, 403, 837, 369, 800, 45, 75, 361, 80, 516, 1268, 216,
  362, 72, 38, 37, 468, 1737, 219, 224, 972, 1272, 2, 685, 288, 721, 252, 2280, 9, 801, 368, 1015, 1,
  291, 255, 360, 296, 260, 363, 4, 2270, 512, 84, 148, 759, 12, 1155, 579, 326, 2024, 7, 151, 333,
  76, 79, 325, 156, 763, 732, 472, 688, 506, 544, 480, 768, 724, 619, 585, 796, 577, 799, 624, 505,
  547, 696, 720, 253, 327, 580, 181, 324, 261, 548, 182, 218, 1416, 1080, 225, 332, 189, 254, 217,
  1189, 2132, 1912, 943, 1052, 648, 944, 650, 1696, 1804, 432, 441, 1046, 1956, 660, 2018, 436, 2053,
  1845, 1659, 2484, 1629, 656, 652, 1048, 2528, 433, 435, 945, 1044, 940, 444, 2521, 1980, 1773,
  2919, 649]

@[expose] def levelsT (Q : RawSchreierDatum n) : List (List (VP n)) :=
  (List.finRange Q.baseCount).map fun i => transV (levelV (strongV Q) Q.base i)

@[expose] def pairsOf : List (List (VP n)) → List (VP n × VP n)
  | [] => [(oneV n, oneV n)]
  | T :: Ts => T.flatMap fun t => (productsV Ts).map fun r => (t, r)

@[expose] def ptq (t r : VP n) : Bool :=
  Nat.beq (fd (wd n) t.1.1 (fd (wd n) r.1.1 (fd (wd n) t.1.1 (fd (wd n) r.1.1 0)))) 0 &&
    Nat.beq (fd (wd n) t.1.1 (fd (wd n) r.1.1 (fd (wd n) t.1.1 (fd (wd n) r.1.1 1)))) 1

@[expose] def invT (c : VP n) : Bool :=
  (List.range n).all fun i => Nat.beq (fd (wd n) c.1.1 (fd (wd n) c.1.1 i)) i

@[expose] def isOuterInvV (QP : RawSchreierDatum n) (c : VP n) : Bool :=
  invT c && !siftV (levelsV (strongV QP) QP.base 0) c

@[expose] def conjAtIdxV (LV : List (VP n)) (t0 c : VP n) (w : ℕ) : Bool :=
  match (LV.drop w).head? with
  | some s => Nat.beq (mulV (mulV s t0) (invV s)).1.1 c.1.1
  | none => false

@[expose] def conjWalkQ (QP : RawSchreierDatum n) (LV : List (VP n)) (t0 : VP n) :
    List (VP n × VP n) → List ℕ → Bool
  | [], _ => true
  | p :: rest, ws => if ptq p.1 p.2 && isOuterInvV QP (mulV p.1 p.2) then
      (match ws with
        | w :: ws' => conjAtIdxV LV t0 (mulV p.1 p.2) w && conjWalkQ QP LV t0 rest ws'
        | [] => false)
    else conjWalkQ QP LV t0 rest ws

@[expose] def conjRepAtQ (QP : RawSchreierDatum n) (LV : List (VP n)) (i : ℕ)
    (ws : List ℕ) (M : List (VP n × VP n)) : Bool :=
  match (LV.drop i).head? with
  | some t0 => isOuterInvV QP t0 && conjWalkQ QP LV t0 M ws
  | none => false

theorem elemsV_eq_pairs (Q : RawSchreierDatum n) :
    elemsV Q = (pairsOf (levelsT Q)).map fun p => pkp p.1 * pkp p.2 := by
  unfold elemsV enumV
  change (productsV (levelsT Q)).map pkp = _
  generalize levelsT Q = Ts
  cases Ts with
  | nil => simp [productsV, pairsOf, pkp_oneV]
  | cons T Ts =>
    simp only [productsV, pairsOf, List.map_flatMap, List.map_map]
    congr 1
    funext t
    apply List.map_congr_left
    intro r _
    simp [pkp_mulV]

theorem ptq_of_sq (hn : 1 < n) {t r : VP n} (h : (pkp t * pkp r) ^ 2 = 1) : ptq t r = true := by
  have h0 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨0, by omega⟩ : Nat)) h
  have h1 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨1, hn⟩ : Nat)) h
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, pkp_apply] at h0 h1
  unfold ptq
  simp only [Bool.and_eq_true, Nat.beq_eq]
  exact ⟨h0, h1⟩

theorem ptq_and (hn : 1 < n) (QP : RawSchreierDatum n) (t r : VP n) :
    (ptq t r && isOuterInv QP (pkp t * pkp r)) = isOuterInv QP (pkp t * pkp r) := by
  cases h : isOuterInv QP (pkp t * pkp r)
  · simp
  · have h' := h
    simp only [isOuterInv, Bool.and_eq_true, decide_eq_true_eq] at h'
    simp [ptq_of_sq hn h'.1]

theorem invT_eq (c : VP n) : invT c = decide ((pkp c) ^ 2 = 1) := by
  rw [Bool.eq_iff_iff, invT, List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro h
    refine Equiv.ext fun i => Fin.ext ?_
    have hi := h i (List.mem_range.2 i.2)
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, pkp_apply]
    simpa only [Nat.beq_eq] using hi
  · intro h i hi
    have h0 := congrArg (fun σ : Equiv.Perm (Fin n) => (σ ⟨i, List.mem_range.1 hi⟩ : Nat)) h
    simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, pkp_apply] at h0
    simpa only [Nat.beq_eq] using h0

theorem sift_pkp (Q : RawSchreierDatum n) (c : VP n) (i : ℕ) :
    Q.sift (pkp c) i = siftV (levelsV (strongV Q) Q.base i) c := by
  rw [RawSchreierDatum.sift, siftLevels_eq Q _ (strongV_map Q), sift_map]

theorem isOuterInvV_eq (QP : RawSchreierDatum n) (c : VP n) :
    isOuterInvV QP c = isOuterInv QP (pkp c) := by
  rw [isOuterInvV, isOuterInv, invT_eq, sift_pkp]

theorem pkp_eq_of_code {a b : VP n} (h : a.1.1 = b.1.1) : pkp a = pkp b :=
  Equiv.ext fun i => Fin.ext (by rw [pkp_apply, pkp_apply, h])

theorem conjAtIdxV_sound {LV : List (VP n)} {t0 c : VP n} {w : ℕ}
    (h : conjAtIdxV LV t0 c w = true) : conjAtIdx (LV.map pkp) (pkp t0) (pkp c) w = true := by
  unfold conjAtIdxV at h
  split at h
  · next s hs =>
    have hd : ((LV.map pkp).drop w).head? = some (pkp s) := by
      rw [← List.map_drop, List.head?_map, hs]
      rfl
    unfold conjAtIdx
    rw [hd]
    dsimp only
    apply decide_eq_true
    rw [← pkp_invV, ← pkp_mulV, ← pkp_mulV]
    exact pkp_eq_of_code (Nat.eq_of_beq_eq_true h)
  · exact absurd h Bool.false_ne_true

theorem conjWalkQ_sound (hn : 1 < n) (QP : RawSchreierDatum n) (LV : List (VP n)) (t0 : VP n) :
    ∀ (M : List (VP n × VP n)) (ws : List ℕ), conjWalkQ QP LV t0 M ws = true →
      conjWalk QP (LV.map pkp) (pkp t0) (M.map fun p => pkp p.1 * pkp p.2) ws = true
  | [], _, _ => rfl
  | p :: rest, ws, h => by
    have e : (ptq p.1 p.2 && isOuterInvV QP (mulV p.1 p.2)) =
        isOuterInv QP (pkp p.1 * pkp p.2) := by
      rw [isOuterInvV_eq, pkp_mulV, ptq_and hn]
    simp only [conjWalkQ, e] at h
    simp only [List.map_cons, conjWalk]
    by_cases ho : isOuterInv QP (pkp p.1 * pkp p.2) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases ws with
      | nil => exact absurd h Bool.false_ne_true
      | cons w ws' =>
        simp only [Bool.and_eq_true] at h ⊢
        have h1 := conjAtIdxV_sound h.1
        rw [pkp_mulV] at h1
        exact ⟨h1, conjWalkQ_sound hn QP LV t0 rest ws' h.2⟩
    · simp only [ho] at h ⊢
      exact conjWalkQ_sound hn QP LV t0 rest ws h

theorem conjRepAt_of_Q (hn : 1 < n) {QP Q : RawSchreierDatum n} {i : ℕ} {ws : List ℕ}
    (h : conjRepAtQ QP (enumV (strongV Q) Q.base) i ws (pairsOf (levelsT Q)) = true) :
    conjRepAt QP (elemsV Q) i ws = true := by
  unfold conjRepAtQ at h
  split at h
  · next t0 ht0 =>
    rw [Bool.and_eq_true, isOuterInvV_eq] at h
    have hd : ((elemsV Q).drop i).head? = some (pkp t0) := by
      rw [elemsV, ← List.map_drop, List.head?_map, ht0]
      rfl
    have hw := conjWalkQ_sound hn QP _ t0 _ ws h.2
    rw [← elemsV_eq_pairs] at hw
    unfold conjRepAt
    rw [hd]
    dsimp only
    rw [Bool.and_eq_true]
    exact ⟨h.1, hw⟩
  · exact absurd h Bool.false_ne_true

theorem conjRep_5012K :
    conjRepAtQ L33.QP (enumV (strongV L33.QA) L33.QA.base) 1405 conjWs
      (pairsOf (levelsT L33.QA)) = true := by
  decide +kernel

theorem conj_5012K : outerConjCheck L33.QP (elemsV L33.QA) = true :=
  outerConjCheck_of_rep (conjRepAt_of_Q (by decide) conjRep_5012K)

theorem comm_5012K : repCommAt L33.QP (elemsV L33.QA) (elemsV L33.QP) 1405 3 1237 = true := by
  decide +kernel

end CertificateChecks.KernelSchreierFam
