module

public import Certificates.Kernel.G24B.Glue
public import Certificates.Kernel.G24B.Checks733008
import CFSG.Walter.J1.Tools
public import CFSG.Certificates.Kernel.G24Wit.Sound
public import CFSG.Quasithin.Recognition.St84.G24BorelFacts
public import Certificates.Data.ExceptionalSL3
public import Certificates.Kernel.G24B.RecChecks

public section

noncomputable section

namespace CFSG.KD.G24B

open CFSG.Fischer CFSG.Quasithin.F112R.St84.G24M CFSG.KC.Misc.Spec CFSG.KC.F2BfsRec
open CFSG.KC.Misc.G24 (mulF2 oneF2 wordF4 nthV nthL)
open CFSG.Quasithin.St84.G24Ident (k1 k2 xa xb a1 b1 a2 b2 pc1 pc2)

theorem andB_iff {a b : Bool} : CFSG.KLie.CT.andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [CFSG.KLie.CT.andB]

theorem notB_iff {a : Bool} : CFSG.KLie.CT.notB a = true ↔ a = false := by
  cases a <;> simp [CFSG.KLie.CT.notB]

theorem allN_iff' {n : ℕ} {f : ℕ → Bool} : CFSG.KLie.CT.allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ n ih =>
    change CFSG.KLie.CT.andB (f n) (CFSG.KLie.CT.allN n f) = true ↔ _
    rw [andB_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem beq_iff' {a b : ℕ} : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

@[expose] def yW (gs : List Y) (u : List ℕ) : Y := (u.map fun c => gs.getD (c / 2) 1).prod

theorem pk_wordF4 {L : List ℕ} {gs : List Y}
    (hg : ∀ i < gs.length, pkMat 28 (L.getD i 0) = psi (gs.getD i 1)) :
    ∀ u : List ℕ, (∀ c ∈ u, c / 2 < gs.length) → pkMat 28 (wordF4 L u) = psi (yW gs u)
  | [], _ => by
    change pkMat 28 (oneF2 28) = psi (List.prod [])
    rw [pkMat_oneF2, List.prod_nil, map_one]
  | c :: u, hu => by
    change pkMat 28 (mulF2 28 (nthV L (c / 2)) (wordF4 L u)) = psi ((gs.getD (c / 2) 1) * yW gs u)
    rw [pkMat_mulF2, nthV_eq, hg _ (hu c (by simp)),
      pk_wordF4 hg u (fun c' hc' => hu c' (by simp [hc'])), map_mul]

theorem yW_mem {H : Subgroup Y} {gs : List Y} (hg : ∀ g ∈ gs, g ∈ H) (u : List ℕ) :
    yW gs u ∈ H := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
  by_cases h : c / 2 < gs.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hg _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact H.one_mem

theorem getD_map_lt {α β : Type} {f : α → β} {L : List α} {j : ℕ} (h : j < L.length) (d : β)
    (d' : α) : (L.map f).getD j d = f (L.getD j d') := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

@[expose] def gsB : List Y := [k1Y, k2Y, xaY, xbY]

@[expose] def gsM (n : Y) : List Y := [k1Y, k2Y, xaY, xbY, n]

theorem psi_k1 (hC : ChevFacts) : psi k1Y = pkMat 28 (blowW k1) := psi_agY hC _
theorem psi_k2 (hC : ChevFacts) : psi k2Y = pkMat 28 (blowW k2) := psi_agY hC _
theorem psi_xa (hC : ChevFacts) : psi xaY = pkMat 28 (blowW xa) := psi_agY hC _
theorem psi_xb (hC : ChevFacts) : psi xbY = pkMat 28 (blowW xb) := psi_agY hC _

theorem pk_gK (hC : ChevFacts) : ∀ i < gsB.length, pkMat 28 (gK.getD i 0) = psi (gsB.getD i 1) := by
  intro i hi
  change i < 4 at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;>
    simp only [gK, gsB, List.getD_cons_succ, List.getD_cons_zero]
  · exact (psi_k1 hC).symm
  · exact (psi_k2 hC).symm
  · exact (psi_xa hC).symm
  · exact (psi_xb hC).symm

theorem pk_gMK (hC : ChevFacts) {n : ℕ} {ny : Y} (hn : psi ny = pkMat 28 n) :
    ∀ i < (gsM ny).length, pkMat 28 ((gMK n).getD i 0) = psi ((gsM ny).getD i 1) := by
  intro i hi
  change i < 5 at hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [gMK, gsM, List.getD_cons_succ, List.getD_cons_zero]
  · exact (psi_k1 hC).symm
  · exact (psi_k2 hC).symm
  · exact (psi_xa hC).symm
  · exact (psi_xb hC).symm
  · exact hn.symm

theorem strOf_nil : CFSG.KC.Misc.G24.strOf [] = "" := rfl

theorem psi_xY (hC : ChevFacts) (i : Fin 2) (c : F4) :
    psi (xY i c) = pkMat 28 (bX (4 * (CFSG.Quasithin.G2U.ix i).val + c.code.val)) := by
  rw [hC.xY_eq_agY, psi_agY hC, blowW, bX, lettersOf_eq, parseK_eq, nthL_eq]
  unfold CFSG.LieType.Multipliers.G24.genWordX
  rw [CFSG.KD.Misc.G24.bX, ← strOf_nil, List.getD_map]
  rfl

theorem psi_yY (hC : ChevFacts) (i : Fin 2) (c : F4) :
    psi (yY i c) = pkMat 28 (bY (4 * (CFSG.Quasithin.G2U.ix i).val + c.code.val)) := by
  rw [hC.yY_eq_agY, psi_agY hC, blowW, bY, lettersOf_eq, parseK_eq, nthL_eq]
  unfold CFSG.LieType.Multipliers.G24.genWordY
  rw [CFSG.KD.Misc.G24.bY, ← strOf_nil, List.getD_map]
  rfl

theorem ix_val (i : Fin 2) : (CFSG.Quasithin.G2U.ix i).val = i.val := by
  fin_cases i <;> rfl

theorem code_one : (1 : F4).code.val = 1 := by decide
theorem code_omega : F4.ω.code.val = 2 := by decide
theorem code_omega2 : (F4.ω * F4.ω).code.val = 3 := by decide

theorem psi_nY (hC : ChevFacts) (i : Fin 2) : psi (nY i) = pkMat 28 (bN i.val) := by
  rw [hC.nY_eq, map_mul, map_mul, psi_xY hC, psi_yY hC, ix_val, code_one]
  change _ = pkMat 28 (mulF2 28 _ (mulF2 28 _ _))
  rw [pkMat_mulF2, pkMat_mulF2, mul_assoc]
  rfl

theorem psi_hY (hC : ChevFacts) (i : Fin 2) : psi (hY i) = pkMat 28 (bH i.val) := by
  rw [hC.hY_eq, map_mul, map_mul, map_mul, psi_xY hC, psi_yY hC, psi_nY hC, ix_val, code_omega,
    code_omega2]
  change _ = pkMat 28 (mulF2 28 _ (mulF2 28 _ (mulF2 28 _ _)))
  rw [pkMat_mulF2, pkMat_mulF2, pkMat_mulF2, mul_assoc, mul_assoc]
  rfl

structure GensParts : Prop where
  shape : (CFSG.Quasithin.St84.G24DC.Native.gBN ()).toList.all
    (fun A => CFSG.KC.Misc.G24.shape4 (CFSG.KC.G24Wit.digsN A)) = true
  gb : (gK == CFSG.KC.G24Wit.gbK) = true
  k1h : blowW k1 = mulF2 28 (bH 0) (mulF2 28 (bH 0) (bH 1))
  k2h : blowW k2 = bH 1
  xax : blowW xa = bX 5
  xbx : blowW xb = bX 1
  k1o : ord3K (blowW k1) = true
  k2o : ord3K (blowW k2) = true
  xao : ord2K (blowW xa) = true
  xbo : ord2K (blowW xb) = true
  n0 : mulF2 28 (bN 0) (bN 0) = oneF2 28
  n1 : mulF2 28 (bN 1) (bN 1) = oneF2 28
  k1k2 : commK (blowW k1) (blowW k2) = true
  k1xa : commK (blowW k1) (blowW xa) = true
  k2xb : commK (blowW k2) (blowW xb) = true

theorem gensParts : GensParts := by
  have h := ch733008_gens
  simp only [gensK, andB_iff, beq_iff'] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

theorem ord3_spec {X : ℕ} (h : ord3K X = true) :
    mulF2 28 (mulF2 28 X X) X = oneF2 28 ∧ X ≠ oneF2 28 := by
  obtain ⟨h1, h2⟩ := andB_iff.mp h
  refine ⟨beq_iff'.mp h1, fun e => ?_⟩
  have h3 := notB_iff.mp h2
  rw [e, Nat.beq_refl] at h3
  exact Bool.noConfusion h3

theorem ord2_spec {X : ℕ} (h : ord2K X = true) : mulF2 28 X X = oneF2 28 ∧ X ≠ oneF2 28 := by
  obtain ⟨h1, h2⟩ := andB_iff.mp h
  refine ⟨beq_iff'.mp h1, fun e => ?_⟩
  have h3 := notB_iff.mp h2
  rw [e, Nat.beq_refl] at h3
  exact Bool.noConfusion h3

theorem orderOf_eq_of_pk (hC : ChevFacts) {y : Y} {X : ℕ} (hy : psi y = pkMat 28 X)
    {p : ℕ} [hp : Fact p.Prime] (hX : X < 2 ^ (28 * 28)) (hpow : psi y ^ p = 1)
    (hne : X ≠ oneF2 28) : orderOf y = p := by
  refine orderOf_eq_prime ?_ ?_
  · exact psi_injective hC (by rw [map_pow, hpow, map_one])
  · intro h1
    exact hne ((pk_one_iff hX).mp (by rw [← hy, h1, map_one]))

theorem blowW_lt (w : List (Fin 6 × Bool)) : blowW w < 2 ^ (28 * 28) := wordF4_lt _ _

theorem orderOf_k1Y' (hC : ChevFacts) : orderOf k1Y = 3 := by
  have hy : psi k1Y = pkMat 28 (blowW k1) := psi_agY hC _
  obtain ⟨h1, h2⟩ := ord3_spec gensParts.k1o
  refine orderOf_eq_of_pk hC hy (blowW_lt _) ?_ h2
  rw [hy, pow_succ, pow_two, ← pkMat_mulF2, ← pkMat_mulF2, h1, pkMat_oneF2]

theorem orderOf_k2Y' (hC : ChevFacts) : orderOf k2Y = 3 := by
  have hy : psi k2Y = pkMat 28 (blowW k2) := psi_agY hC _
  obtain ⟨h1, h2⟩ := ord3_spec gensParts.k2o
  refine orderOf_eq_of_pk hC hy (blowW_lt _) ?_ h2
  rw [hy, pow_succ, pow_two, ← pkMat_mulF2, ← pkMat_mulF2, h1, pkMat_oneF2]

theorem orderOf_xaY' (hC : ChevFacts) : orderOf xaY = 2 := by
  have hy : psi xaY = pkMat 28 (blowW xa) := psi_agY hC _
  obtain ⟨h1, h2⟩ := ord2_spec gensParts.xao
  refine orderOf_eq_of_pk hC hy (blowW_lt _) ?_ h2
  rw [hy, pow_two, ← pkMat_mulF2, h1, pkMat_oneF2]

theorem orderOf_xbY' (hC : ChevFacts) : orderOf xbY = 2 := by
  have hy : psi xbY = pkMat 28 (blowW xb) := psi_agY hC _
  obtain ⟨h1, h2⟩ := ord2_spec gensParts.xbo
  refine orderOf_eq_of_pk hC hy (blowW_lt _) ?_ h2
  rw [hy, pow_two, ← pkMat_mulF2, h1, pkMat_oneF2]

theorem commute_of_pk (hC : ChevFacts) {x y : Y} {X Z : ℕ} (hx : psi x = pkMat 28 X)
    (hy : psi y = pkMat 28 Z) (h : commK X Z = true) : Commute x y := by
  refine psi_injective hC ?_
  rw [map_mul, map_mul, hx, hy, ← pkMat_mulF2, ← pkMat_mulF2, beq_iff'.mp h]

theorem commute_k1Y_k2Y' (hC : ChevFacts) : Commute k1Y k2Y :=
  commute_of_pk hC (psi_agY hC _) (psi_agY hC _) gensParts.k1k2

theorem commute_k1Y_xaY' (hC : ChevFacts) : Commute k1Y xaY :=
  commute_of_pk hC (psi_agY hC _) (psi_agY hC _) gensParts.k1xa

theorem commute_k2Y_xbY' (hC : ChevFacts) : Commute k2Y xbY :=
  commute_of_pk hC (psi_agY hC _) (psi_agY hC _) gensParts.k2xb

theorem k1Y_eq (hC : ChevFacts) : k1Y = hY 0 * hY 0 * hY 1 := by
  refine psi_injective hC ?_
  rw [map_mul, map_mul, psi_hY hC, psi_hY hC, psi_k1 hC, gensParts.k1h, pkMat_mulF2, pkMat_mulF2,
    mul_assoc]
  rfl

theorem k2Y_eq (hC : ChevFacts) : k2Y = hY 1 := by
  refine psi_injective hC ?_
  rw [psi_hY hC, psi_k2 hC, gensParts.k2h]
  rfl

theorem xaY_eq (hC : ChevFacts) : xaY = xY 1 1 := by
  refine psi_injective hC ?_
  rw [psi_xY hC, psi_xa hC, gensParts.xax, ix_val, code_one]
  rfl

theorem xbY_eq (hC : ChevFacts) : xbY = xY 0 1 := by
  refine psi_injective hC ?_
  rw [psi_xY hC, psi_xb hC, gensParts.xbx, ix_val, code_one]
  rfl

theorem gB0_mem_B0' (hC : ChevFacts) (k : Fin 4) : gB0 k ∈ B0 := by
  fin_cases k
  · change k1Y ∈ B0
    rw [k1Y_eq hC]
    exact B0.mul_mem (B0.mul_mem (hC.hY_mem_B0 0) (hC.hY_mem_B0 0)) (hC.hY_mem_B0 1)
  · change k2Y ∈ B0
    rw [k2Y_eq hC]
    exact hC.hY_mem_B0 1
  · change xaY ∈ B0
    rw [xaY_eq hC]
    exact hC.xY_mem_B0 1 1
  · change xbY ∈ B0
    rw [xbY_eq hC]
    exact hC.xY_mem_B0 0 1

theorem toGL_gB0' (hC : ChevFacts) (k : Fin 4) :
    (toGL (gB0 k) : Matrix (Fin 14) (Fin 14) F4) =
      CFSG.Quasithin.St84.G24DC.Code.decode
        ((CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val
          CFSG.Quasithin.St84.G24DC.Native.oneM) := by
  have hgb : gK = CFSG.KC.G24Wit.gbK := beq_iff_eq.mp gensParts.gb
  have hsz : (CFSG.Quasithin.St84.G24DC.Native.gBN ()).size = 4 := rfl
  have hk : k.val < (CFSG.Quasithin.St84.G24DC.Native.gBN ()).size := by rw [hsz]; exact k.2
  have hget : (CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val
      CFSG.Quasithin.St84.G24DC.Native.oneM = (CFSG.Quasithin.St84.G24DC.Native.gBN ())[k.val] := by
    unfold Array.getD
    rw [dif_pos hk]
    rfl
  have hmem : (CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val
      CFSG.Quasithin.St84.G24DC.Native.oneM ∈ (CFSG.Quasithin.St84.G24DC.Native.gBN ()).toList := by
    rw [hget]
    exact Array.getElem_mem_toList hk
  have hs := List.all_eq_true.mp gensParts.shape _ hmem
  have e3 : CFSG.KC.G24Wit.gbK.getD k.val 0 = CFSG.KC.G24Wit.decK
      ((CFSG.Quasithin.St84.G24DC.Native.gBN ()).getD k.val CFSG.Quasithin.St84.G24DC.Native.oneM) := by
    unfold CFSG.KC.G24Wit.gbK
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, Array.getElem_toList, hget]
  apply blowMat_injective
  rw [CFSG.KC.G24Wit.decode_eq_digMat, ← pkMat_blow14 hs, ← psi_apply]
  have e2 : psi (gB0 k) = pkMat 28 (gK.getD k.val 0) := by
    rw [pk_gK hC k.val k.2, show gB0 k = gsB.getD k.val 1 by fin_cases k <;> rfl]
  rw [e2, hgb, e3]
  rfl

theorem pins_spec {lb ng : ℕ} {CF : ℕ → ℕ} {ws : List (List (Fin 6 × Bool))}
    (h : pinsK lb ng CF ws = true) : ∀ j < ng, genR 28 12 lb ng CF j = blowW (ws.getD j []) := by
  obtain ⟨-, h2⟩ := andB_iff.mp h
  exact fun j hj => beq_iff'.mp (allN_iff'.mp h2 j hj)

theorem recOK_of (hC : ChevFacts) {ng lb N : ℕ} {CF : ℕ → ℕ} {S : Fin ng → Y}
    {ws : List (List (Fin 6 × Bool))} (hSw : ∀ j : Fin ng, S j = agY (ws.getD j.val []))
    (hp : pinsK lb ng CF ws = true) (hN : 0 < N) (hNw : N < 2 ^ 12)
    (hh : headK 28 12 lb ng CF = true) (h : ∀ k < N, recK2 28 12 lb ng CF (genR 28 12 lb ng CF) N k = true) :
    RecOK S lb CF (genR 28 12 lb ng CF) N :=
  ⟨fun j => by rw [hSw, psi_agY hC, pins_spec hp j j.2], hN, hNw, hh, h⟩

theorem rQ1 (hC : ChevFacts) : RecOK pc1Y 6 EQ1.CF (genR 28 12 6 10 EQ1.CF) 1024 :=
  recOK_of hC (ws := wQ1) (fun _ => rfl) ch733008_q1Pins (by norm_num) (by norm_num) ch733008_q1Head
    ch733008_q1Recs

theorem rQ2 (hC : ChevFacts) : RecOK pc2Y 6 EQ2.CF (genR 28 12 6 10 EQ2.CF) 1024 :=
  recOK_of hC (ws := wQ2) (fun _ => rfl) ch733008_q2Pins (by norm_num) (by norm_num) ch733008_q2Head
    ch733008_q2Recs

theorem rA1 (hC : ChevFacts) : RecOK A1gen 6 EA1.CF (genR 28 12 6 3 EA1.CF) 180 :=
  recOK_of hC (ws := wA1) (fun j => by fin_cases j <;> rfl) ch733008_a1Pins (by norm_num) (by norm_num)
    ch733008_a1Head ch733008_a1Recs

theorem rA2 (hC : ChevFacts) : RecOK A2gen 6 EA2.CF (genR 28 12 6 3 EA2.CF) 180 :=
  recOK_of hC (ws := wA2) (fun j => by fin_cases j <;> rfl) ch733008_a2Pins (by norm_num) (by norm_num)
    ch733008_a2Head ch733008_a2Recs

@[expose] def hGen : Fin 2 → Y := ![k1Y, k2Y]

theorem H0_eq : CFSG.Quasithin.F112R.St84.G24M.H0 = Subgroup.closure (Set.range hGen) := by
  have e : Set.range hGen = ({k1Y, k2Y} : Set Y) := by
    rw [hGen, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  rw [e]

theorem rH (hC : ChevFacts) : RecOK hGen 6 EH.CF (genR 28 12 6 2 EH.CF) 9 :=
  recOK_of hC (ws := wH) (fun j => by fin_cases j <;> rfl) ch733008_hPins (by norm_num) (by norm_num)
    ch733008_hHead ch733008_hRecs

theorem card_Q1' (hC : ChevFacts) : Nat.card Q1 = 1024 := card_of_recOK hC (rQ1 hC)
theorem card_Q2' (hC : ChevFacts) : Nat.card Q2 = 1024 := card_of_recOK hC (rQ2 hC)
theorem card_A1' (hC : ChevFacts) : Nat.card A1 = 180 := card_of_recOK hC (rA1 hC)
theorem card_A2' (hC : ChevFacts) : Nat.card A2 = 180 := card_of_recOK hC (rA2 hC)
theorem card_H0' (hC : ChevFacts) : Nat.card CFSG.Quasithin.F112R.St84.G24M.H0 = 9 := by
  rw [H0_eq]
  exact card_of_recOK hC (rH hC)

structure ParaParts (EQ EA : ℕ → ℕ) (GQ GA : List ℕ) (n : ℕ) (pcB aM dq da : List (List ℕ))
    (nm dj : List ℕ) : Prop where
  pc : ∀ j < 10, nthV GQ j = wordF4 gK (nthL pcB j)
  ag : ∀ t < 3, nthV GA t = wordF4 (gMK n) (nthL aM t)
  dec : ∀ x < 5, nthV (gMK n) x = mulF2 28 (wordF4 GQ (nthL dq x)) (wordF4 GA (nthL da x))
  disj : ∀ s < 180, sortedAt 28 12 6 3 EA s = oneF2 28 ∨
    gapK 28 12 6 10 EQ 1024 (nthV dj s) (sortedAt 28 12 6 3 EA s) = true
  norm : ∀ x < 5, ∀ j < 10, nthV nm (10 * x + j) < 1024 ∧
    sortedAt 28 12 6 10 EQ (nthV nm (10 * x + j)) =
      mulF2 28 (mulF2 28 (nthV (gMK n) x) (nthV GQ j)) (nthV (gMiK n) x)

theorem paraParts {EQ EA : ℕ → ℕ} {GQ GA : List ℕ} {n : ℕ} {pcB aM dq da : List (List ℕ)}
    {nm dj : List ℕ} (h : paraK EQ EA GQ GA n pcB aM dq da nm dj = true) :
    ParaParts EQ EA GQ GA n pcB aM dq da nm dj := by
  unfold paraK at h
  obtain ⟨h1, h⟩ := andB_iff.mp h
  obtain ⟨h2, h⟩ := andB_iff.mp h
  obtain ⟨h3, h⟩ := andB_iff.mp h
  obtain ⟨h4, h5⟩ := andB_iff.mp h
  refine ⟨fun j hj => beq_iff'.mp (allN_iff'.mp h1 j hj),
    fun t ht => beq_iff'.mp (allN_iff'.mp h2 t ht),
    fun x hx => beq_iff'.mp (allN_iff'.mp h3 x hx), fun s hs => ?_, fun x hx j hj => ?_⟩
  · have e := allN_iff'.mp h4 s hs
    rw [strictB_eq'] at e
    cases hX : Nat.beq (sortedAt 28 12 6 3 EA s) (oneF2 28)
    · rw [hX] at e
      exact Or.inr e
    · exact Or.inl (beq_iff'.mp hX)
  · have e := allN_iff'.mp (allN_iff'.mp h5 x hx) j hj
    rw [strictB_eq'] at e
    obtain ⟨e1, e2⟩ := andB_iff.mp e
    exact ⟨Nat.le_of_ble_eq_true e1, beq_iff'.mp e2⟩

@[expose] def gsL {m : ℕ} (S : Fin m → Y) : List Y := List.ofFn S

theorem gsL_getD {m : ℕ} (S : Fin m → Y) {i : ℕ} (hi : i < m) : (gsL S).getD i 1 = S ⟨i, hi⟩ := by
  rw [gsL, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem gsL_length {m : ℕ} (S : Fin m → Y) : (gsL S).length = m := List.length_ofFn

theorem pk_gsL (hC : ChevFacts) {m : ℕ} (S : Fin m → Y) (ws : List (List (Fin 6 × Bool)))
    (hlen : ws.length = m) (hSw : ∀ j : Fin m, S j = agY (ws.getD j.val [])) :
    ∀ i < (gsL S).length, pkMat 28 ((ws.map blowW).getD i 0) = psi ((gsL S).getD i 1) := by
  intro i hi
  rw [gsL_length] at hi
  rw [gsL_getD S hi, hSw, psi_agY hC, getD_map_lt (by omega) 0 []]

@[expose] def gsMi (n : Y) : List Y := [k1Y⁻¹, k2Y⁻¹, xaY⁻¹, xbY⁻¹, n⁻¹]

theorem inv_of_cube {x : Y} {X : ℕ} (hC : ChevFacts) (hx : psi x = pkMat 28 X)
    (h : mulF2 28 (mulF2 28 X X) X = oneF2 28) : x⁻¹ = x * x := by
  have h' : pkMat 28 X * pkMat 28 X * pkMat 28 X = 1 := by
    rw [← pkMat_mulF2, ← pkMat_mulF2, h, pkMat_oneF2]
  refine inv_eq_of_mul_eq_one_right (psi_injective hC ?_)
  rw [map_mul, map_mul, map_one, hx, ← mul_assoc, h']

theorem inv_of_sq {x : Y} {X : ℕ} (hC : ChevFacts) (hx : psi x = pkMat 28 X)
    (h : mulF2 28 X X = oneF2 28) : x⁻¹ = x := by
  refine inv_eq_of_mul_eq_one_right (psi_injective hC ?_)
  rw [map_mul, map_one, hx, ← pkMat_mulF2, h, pkMat_oneF2]

theorem pk_gMiK (hC : ChevFacts) {n : ℕ} {ny : Y} (hn : psi ny = pkMat 28 n)
    (hn2 : mulF2 28 n n = oneF2 28) :
    ∀ i < 5, pkMat 28 ((gMiK n).getD i 0) = psi ((gsMi ny).getD i 1) := by
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
    simp only [gMiK, gsMi, List.getD_cons_succ, List.getD_cons_zero]
  · rw [inv_of_cube hC (psi_k1 hC) (ord3_spec gensParts.k1o).1, map_mul, psi_k1 hC, pkMat_mulF2]
  · rw [inv_of_cube hC (psi_k2 hC) (ord3_spec gensParts.k2o).1, map_mul, psi_k2 hC, pkMat_mulF2]
  · rw [inv_of_sq hC (psi_xa hC) (ord2_spec gensParts.xao).1, psi_xa hC]
  · rw [inv_of_sq hC (psi_xb hC) (ord2_spec gensParts.xbo).1, psi_xb hC]
  · rw [inv_of_sq hC hn hn2, hn]

theorem pc_mem_closure (hC : ChevFacts) {EQ EA : ℕ → ℕ} {GA : List ℕ} {n : ℕ}
    {pcB aM dq da : List (List ℕ)} {nm dj : List ℕ} {S : Fin 10 → Y}
    {ws : List (List (Fin 6 × Bool))} (hlen : ws.length = 10)
    (hSw : ∀ j : Fin 10, S j = agY (ws.getD j.val []))
    (hP : ParaParts EQ EA (ws.map blowW) GA n pcB aM dq da nm dj)
    (hb : ∀ j < 10, ∀ c ∈ nthL pcB j, c / 2 < 4) :
    Subgroup.closure (Set.range S) ≤ Subgroup.closure (Set.range gB0) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨j, rfl⟩
  have e : psi (S j) = psi (yW gsB (nthL pcB j.val)) := by
    rw [← pk_wordF4 (pk_gK hC) _ (hb j.val j.2), ← hP.pc j.val j.2, nthV_eq,
      getD_map_lt (by omega) 0 [], hSw, psi_agY hC]
  rw [psi_injective hC e]
  refine yW_mem (fun g hg => ?_) _
  simp only [gsB, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨0, rfl⟩
  · exact Subgroup.subset_closure ⟨1, rfl⟩
  · exact Subgroup.subset_closure ⟨2, rfl⟩
  · exact Subgroup.subset_closure ⟨3, rfl⟩

theorem letters_pcB1 : ∀ j < 10, ∀ c ∈ nthL pcB1 j, c / 2 < 4 := by decide +kernel
theorem letters_pcB2 : ∀ j < 10, ∀ c ∈ nthL pcB2 j, c / 2 < 4 := by decide +kernel

@[expose] def e2Y : Y := k2Y * xaY * (k2Y * k2Y)

@[expose] def cY : Fin 4 → Y := ![1, xaY, e2Y, xaY * e2Y]

theorem psi_e2 (hC : ChevFacts) : psi e2Y = pkMat 28 e2K := by
  rw [e2Y, e2K, map_mul, map_mul, map_mul, psi_k2 hC, psi_xa hC, pkMat_mulF2, pkMat_mulF2,
    pkMat_mulF2]

theorem psi_cY (hC : ChevFacts) (i : Fin 4) : psi (cY i) = pkMat 28 (nthV csK i.val) := by
  rw [nthV_eq]
  fin_cases i <;> simp only [csK, List.getD_cons_succ, List.getD_cons_zero]
  · change psi 1 = _
    rw [map_one, pkMat_oneF2]
  · exact psi_xa hC
  · exact psi_e2 hC
  · change psi (xaY * e2Y) = _
    rw [map_mul, psi_xa hC, psi_e2 hC, pkMat_mulF2]

@[expose] def pairPos (i j : ℕ) : ℕ := nthV cs1 (if i = 0 then j - 1 else if i = 1 then j + 1 else 5)

theorem cos_sq (i : ℕ) (hi : i < 4) : mulF2 28 (nthV csK i) (nthV csK i) = oneF2 28 := by
  have h := ch733008_cosets
  unfold cosK at h
  exact beq_iff'.mp (allN_iff'.mp (andB_iff.mp h).1 i hi)

theorem cos_gap {i j : ℕ} (hij : i < j) (hj : j < 4) :
    gapK 28 12 6 10 EQ1.CF 1024 (pairPos i j) (mulF2 28 (nthV csK i) (nthV csK j)) = true := by
  have h := ch733008_cosets
  unfold cosK at h
  obtain ⟨-, h⟩ := andB_iff.mp h
  obtain ⟨g1, h⟩ := andB_iff.mp h
  obtain ⟨g2, h⟩ := andB_iff.mp h
  obtain ⟨g3, h⟩ := andB_iff.mp h
  obtain ⟨g4, h⟩ := andB_iff.mp h
  obtain ⟨g5, g6⟩ := andB_iff.mp h
  rcases (by omega : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 2) ∨
    (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact g1
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6

theorem cY_inv (hC : ChevFacts) (i : Fin 4) : (cY i)⁻¹ = cY i := by
  refine inv_eq_of_mul_eq_one_right (psi_injective hC ?_)
  rw [map_mul, psi_cY hC, ← pkMat_mulF2, cos_sq i.val i.2, pkMat_oneF2, map_one]

theorem cY_mul_not_mem (hC : ChevFacts) {i j : Fin 4} (hij : i < j) : cY i * cY j ∉ Q1 :=
  not_mem_of_gap (rQ1 hC) (mulF2_lt' _ _) (by rw [map_mul, psi_cY hC, psi_cY hC, pkMat_mulF2])
    (cos_gap (i := i.val) (j := j.val) hij j.2)

theorem cY_inv_mul_not_mem (hC : ChevFacts) {i j : Fin 4} (hij : i ≠ j) :
    (cY i)⁻¹ * cY j ∉ Q1 := by
  rw [cY_inv hC]
  rcases lt_or_gt_of_ne hij with h | h
  · exact cY_mul_not_mem hC h
  · intro hm
    apply cY_mul_not_mem hC h
    have := Q1.inv_mem hm
    rwa [mul_inv_rev, cY_inv hC, cY_inv hC] at this

theorem isPGroup_of_card_two_pow {H : Subgroup Y} {k : ℕ} (h : Nat.card H = 2 ^ k) :
    IsPGroup 2 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card h

theorem k2Y_inv (hC : ChevFacts) : k2Y⁻¹ = k2Y * k2Y :=
  inv_of_cube hC (psi_k2 hC) (ord3_spec gensParts.k2o).1

theorem xaY_mem_T0 (hC : ChevFacts) : xaY ∈ T0 := by
  have hle : Subgroup.zpowers xaY ≤ B0 := by
    rw [Subgroup.zpowers_le]
    exact gB0_mem_B0' hC 2
  have hp : IsPGroup 2 (Subgroup.zpowers xaY) := by
    refine isPGroup_of_card_two_pow (k := 1) ?_
    rw [Nat.card_zpowers, orderOf_xaY' hC, pow_one]
  exact hC.le_T0_of_isPGroup hle hp (Subgroup.mem_zpowers xaY)

theorem e2Y_mem_T0 (hC : ChevFacts) : e2Y ∈ T0 := by
  have hk : k2Y ∈ Subgroup.normalizer (T0 : Set Y) := by
    rw [hC.normalizer_T0]
    exact gB0_mem_B0' hC 1
  rw [e2Y, ← k2Y_inv hC]
  exact (Subgroup.mem_normalizer_iff.mp hk xaY).mp (xaY_mem_T0 hC)

theorem cY_mem_T0 (hC : ChevFacts) (i : Fin 4) : cY i ∈ T0 := by
  fin_cases i
  · exact T0.one_mem
  · exact xaY_mem_T0 hC
  · exact e2Y_mem_T0 hC
  · exact T0.mul_mem (xaY_mem_T0 hC) (e2Y_mem_T0 hC)

theorem gB0_mem_closure (k : Fin 4) : gB0 k ∈ Subgroup.closure (Set.range gB0) :=
  Subgroup.subset_closure ⟨k, rfl⟩

theorem gB0_0 : gB0 0 = k1Y := rfl
theorem gB0_1 : gB0 1 = k2Y := rfl
theorem gB0_2 : gB0 2 = xaY := rfl
theorem cY_mem_closure (i : Fin 4) : cY i ∈ Subgroup.closure (Set.range gB0) := by
  have hk2 := gB0_mem_closure 1
  have hxa := gB0_mem_closure 2
  rw [gB0_1] at hk2
  rw [gB0_2] at hxa
  have he2 : e2Y ∈ Subgroup.closure (Set.range gB0) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk2 hxa) (Subgroup.mul_mem _ hk2 hk2)
  fin_cases i
  · exact Subgroup.one_mem _
  · exact hxa
  · exact he2
  · exact Subgroup.mul_mem _ hxa he2

theorem Q1_le_closure (hC : ChevFacts) : Q1 ≤ Subgroup.closure (Set.range gB0) :=
  pc_mem_closure hC (ws := wQ1) rfl (fun _ => rfl) (paraParts ch733008_para1) letters_pcB1

theorem Q2_le_closure (hC : ChevFacts) : Q2 ≤ Subgroup.closure (Set.range gB0) :=
  pc_mem_closure hC (ws := wQ2) rfl (fun _ => rfl) (paraParts ch733008_para2) letters_pcB2

theorem closure_le_B0 (hC : ChevFacts) : Subgroup.closure (Set.range gB0) ≤ B0 :=
  (Subgroup.closure_le _).mpr (by rintro _ ⟨k, rfl⟩; exact gB0_mem_B0' hC k)

theorem T0_le_closure (hC : ChevFacts) : T0 ≤ Subgroup.closure (Set.range gB0) := by
  set CB := Subgroup.closure (Set.range gB0) with hCB
  have hQT : Q1 ≤ T0 := hC.le_T0_of_isPGroup ((Q1_le_closure hC).trans (closure_le_B0 hC))
    (isPGroup_of_card_two_pow (k := 10) (card_Q1' hC))
  let f : Fin 4 × Q1 → ↥(CB ⊓ T0) := fun p => ⟨cY p.1 * p.2,
    Subgroup.mem_inf.mpr ⟨CB.mul_mem (cY_mem_closure _) (Q1_le_closure hC p.2.2),
      T0.mul_mem (cY_mem_T0 hC _) (hQT p.2.2)⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨i, q⟩ ⟨j, q'⟩ h
    have e : cY i * (q : Y) = cY j * q' := congrArg Subtype.val h
    by_cases hij : i = j
    · subst hij
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel e))
    · exfalso
      apply cY_inv_mul_not_mem hC (Ne.symm hij)
      have e2 : (cY j)⁻¹ * cY i = (q' : Y) * (q : Y)⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, e, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e2]
      exact Q1.mul_mem q'.2 (Q1.inv_mem q.2)
  have hcard : Nat.card T0 ≤ Nat.card ↥(CB ⊓ T0) := by
    rw [hC.card_T0]
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin, card_Q1' hC] at this
  have heq : CB ⊓ T0 = T0 := Subgroup.eq_of_le_of_card_ge inf_le_right hcard
  rw [← heq]
  exact inf_le_left

theorem closure_gB0' (hC : ChevFacts) : Subgroup.closure (Set.range gB0) = B0 := by
  set CB := Subgroup.closure (Set.range gB0) with hCB
  have hle := closure_le_B0 hC
  have hH : CFSG.Quasithin.F112R.St84.G24M.H0 ≤ CB := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · rw [← gB0_0]
      exact gB0_mem_closure 0
    · rw [← gB0_1]
      exact gB0_mem_closure 1
  have h1 : 4096 ∣ Nat.card CB := by
    rw [← hC.card_T0]
    exact Subgroup.card_dvd_of_le (T0_le_closure hC)
  have h2 : 9 ∣ Nat.card CB := by
    rw [← card_H0' hC]
    exact Subgroup.card_dvd_of_le hH
  have h3 : 36864 ∣ Nat.card CB :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2
  have h4 : Nat.card CB ≤ 36864 := by
    rw [← hC.card_B0]
    exact Subgroup.card_le_of_le hle
  have h5 : 0 < Nat.card CB := Nat.card_pos
  have h6 : Nat.card CB = 36864 := by
    obtain ⟨c, hc⟩ := h3
    rcases c with _ | _ | c
    · omega
    · omega
    · omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hC.card_B0, h6])

structure Para (EQ EA : ℕ → ℕ) (wsQ wsA : List (List (Fin 6 × Bool))) (n : ℕ)
    (pcB aM dq da : List (List ℕ)) (nm dj : List ℕ) (SQ : Fin 10 → Y) (SA : Fin 3 → Y) (ny : Y)
    (M : Subgroup Y) : Prop where
  parts : ParaParts EQ EA (wsQ.map blowW) (wsA.map blowW) n pcB aM dq da nm dj
  rQ : RecOK SQ 6 EQ (genR 28 12 6 10 EQ) 1024
  rA : RecOK SA 6 EA (genR 28 12 6 3 EA) 180
  lenQ : wsQ.length = 10
  lenA : wsA.length = 3
  hSQ : ∀ j : Fin 10, SQ j = agY (wsQ.getD j.val [])
  hSA : ∀ t : Fin 3, SA t = agY (wsA.getD t.val [])
  hn : psi ny = pkMat 28 n
  hn2 : mulF2 28 n n = oneF2 28
  hBM : B0 ≤ M
  hnM : ny ∈ M
  hMle : ∀ {H : Subgroup Y}, B0 ≤ H → ny ∈ H → M ≤ H
  bA : ∀ t < 3, ∀ c ∈ nthL aM t, c / 2 < 5
  bq : ∀ x < 5, ∀ c ∈ nthL dq x, c / 2 < 10
  ba : ∀ x < 5, ∀ c ∈ nthL da x, c / 2 < 3

variable {EQ EA : ℕ → ℕ} {wsQ wsA : List (List (Fin 6 × Bool))} {n : ℕ}
  {pcB aM dq da : List (List ℕ)} {nm dj : List ℕ} {SQ : Fin 10 → Y} {SA : Fin 3 → Y} {ny : Y}
  {M : Subgroup Y}

theorem gsM_mem (hC : ChevFacts) (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M) :
    ∀ g ∈ gsM ny, g ∈ M := by
  intro g hg
  simp only [gsM, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact hp.hBM (gB0_mem_B0' hC 0)
  · exact hp.hBM (gB0_mem_B0' hC 1)
  · exact hp.hBM (gB0_mem_B0' hC 2)
  · exact hp.hBM (gB0_mem_B0' hC 3)
  · exact hp.hnM

theorem para_A_le (hC : ChevFacts) (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M) :
    Subgroup.closure (Set.range SA) ≤ M := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨t, rfl⟩
  have e : psi (SA t) = psi (yW (gsM ny) (nthL aM t.val)) := by
    rw [← pk_wordF4 (pk_gMK hC hp.hn) _ (hp.bA t.val t.2), ← hp.parts.ag t.val t.2, nthV_eq,
      getD_map_lt (by rw [hp.lenA]; exact t.2) 0 [], hp.hSA, psi_agY hC]
  rw [psi_injective hC e]
  exact yW_mem (gsM_mem hC hp) _

theorem para_Q_le (hC : ChevFacts) (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M)
    (hQ : Subgroup.closure (Set.range SQ) ≤ Subgroup.closure (Set.range gB0)) :
    Subgroup.closure (Set.range SQ) ≤ M :=
  hQ.trans ((closure_le_B0 hC).trans hp.hBM)

theorem gsM_getD_mem_sup (hC : ChevFacts)
    (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M) {i : ℕ} (hi : i < 5) :
    (gsM ny).getD i 1 ∈ Subgroup.closure (Set.range SQ) ⊔ Subgroup.closure (Set.range SA) := by
  have hq := pk_wordF4 (pk_gsL hC SQ wsQ hp.lenQ hp.hSQ) _
    (by rw [gsL_length]; exact hp.bq i hi)
  have ha := pk_wordF4 (pk_gsL hC SA wsA hp.lenA hp.hSA) _
    (by rw [gsL_length]; exact hp.ba i hi)
  have e : (gsM ny).getD i 1 = yW (gsL SQ) (nthL dq i) * yW (gsL SA) (nthL da i) := by
    refine psi_injective hC ?_
    rw [← pk_gMK hC hp.hn i (by simpa [gsM] using hi), ← nthV_eq, hp.parts.dec i hi, pkMat_mulF2,
      hq, ha, map_mul]
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (yW_mem (fun g hg => ?_) _))
    (Subgroup.mem_sup_right (yW_mem (fun g hg => ?_) _))
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
    exact Subgroup.subset_closure ⟨j, rfl⟩

theorem gB0_eq_gsM (k : Fin 4) : gB0 k = (gsM ny).getD k.val 1 := by
  fin_cases k <;> rfl

theorem para_sup (hC : ChevFacts) (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M)
    (hQ : Subgroup.closure (Set.range SQ) ≤ Subgroup.closure (Set.range gB0)) :
    Subgroup.closure (Set.range SQ) ⊔ Subgroup.closure (Set.range SA) = M := by
  refine le_antisymm (sup_le (para_Q_le hC hp hQ) (para_A_le hC hp)) (hp.hMle ?_ ?_)
  · rw [← closure_gB0' hC]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [gB0_eq_gsM k]
    exact gsM_getD_mem_sup hC hp (by omega)
  · exact gsM_getD_mem_sup hC hp (i := 4) (by omega)

theorem para_inf (hC : ChevFacts) (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M) :
    Subgroup.closure (Set.range SA) ⊓ Subgroup.closure (Set.range SQ) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rintro x ⟨hxA, hxQ⟩
  obtain ⟨t, ht, hx⟩ := exists_entry_of_recOK hp.rA hxA
  obtain ⟨s, hs, es⟩ := exists_sorted_of_entry hp.rA.h ht
  rcases hp.parts.disj s hs with h1 | h1
  · refine Subgroup.mem_bot.mpr (psi_injective hC ?_)
    rw [hx, ← es, h1, pkMat_oneF2, map_one]
  · exact absurd hxQ (not_mem_of_gap hp.rQ (es ▸ CFSG.KC.F2Mat.elemAt_lt _ _ _ _ _ _)
      (by rw [hx, ← es]) h1)

theorem gsMi_getD (i : ℕ) (hi : i < 5) : (gsMi ny).getD i 1 = ((gsM ny).getD i 1)⁻¹ := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem mem_normalizer_of_gens {Q : Subgroup Y} {S : Fin 10 → Y} (hQ : Q = Subgroup.closure (Set.range S))
    {x : Y} (hx : ∀ j : Fin 10, x * S j * x⁻¹ ∈ Q) : x ∈ Subgroup.normalizer (Q : Set Y) := by
  have hmap : Q.map (MulAut.conj x).toMonoidHom ≤ Q := by
    rw [Subgroup.map_le_iff_le_comap, hQ]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨m, rfl⟩
    rw [← hQ]
    simpa [MulAut.conj_apply] using hx m
  refine CFSG.Walter.J1.mem_normalizer_of_conj_mem ?_
  intro z hz
  simpa [MulAut.conj_apply] using hmap ⟨z, hz, rfl⟩

theorem para_normalizer (hC : ChevFacts)
    (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M) :
    M ≤ Subgroup.normalizer (Subgroup.closure (Set.range SQ) : Set Y) := by
  have hconj : ∀ i < 5, ∀ j : Fin 10,
      (gsM ny).getD i 1 * SQ j * ((gsM ny).getD i 1)⁻¹ ∈ Subgroup.closure (Set.range SQ) := by
    intro i hi j
    obtain ⟨hs, he⟩ := hp.parts.norm i hi j.val j.2
    refine mem_of_sorted hC hp.rQ hs ?_
    rw [he, pkMat_mulF2, pkMat_mulF2, map_mul, map_mul, nthV_eq, nthV_eq, nthV_eq,
      pk_gMK hC hp.hn i (by simpa [gsM] using hi), pk_gMiK hC hp.hn hp.hn2 i hi, gsMi_getD i hi,
      getD_map_lt (by rw [hp.lenQ]; exact j.2) 0 [], ← psi_agY hC, ← hp.hSQ]
  refine hp.hMle ?_ ?_
  · rw [← closure_gB0' hC]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨k, rfl⟩
    rw [gB0_eq_gsM k]
    exact mem_normalizer_of_gens rfl (hconj k.val (by omega))
  · exact mem_normalizer_of_gens rfl (hconj 4 (by omega))

theorem para_pCore (hC : ChevFacts) (hp : Para EQ EA wsQ wsA n pcB aM dq da nm dj SQ SA ny M)
    (hQ : Subgroup.closure (Set.range SQ) ≤ Subgroup.closure (Set.range gB0))
    (hcardM : Nat.card (CFSG.Open.pCoreOf 2 M) = 1024) :
    CFSG.Open.pCoreOf 2 M = Subgroup.closure (Set.range SQ) := by
  have hcardQ := card_of_recOK hC hp.rQ
  have hle : Subgroup.closure (Set.range SQ) ≤ CFSG.Open.pCoreOf 2 M :=
    CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (para_Q_le hC hp hQ)
      (para_normalizer hC hp) (isPGroup_of_card_two_pow (k := 10) hcardQ)
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardM, hcardQ])).symm

theorem letters_aM1 : ∀ t < 3, ∀ c ∈ nthL aM1 t, c / 2 < 5 := by decide +kernel
theorem letters_aM2 : ∀ t < 3, ∀ c ∈ nthL aM2 t, c / 2 < 5 := by decide +kernel
theorem letters_dq1 : ∀ x < 5, ∀ c ∈ nthL dq1 x, c / 2 < 10 := by decide +kernel
theorem letters_dq2 : ∀ x < 5, ∀ c ∈ nthL dq2 x, c / 2 < 10 := by decide +kernel
theorem letters_da1 : ∀ x < 5, ∀ c ∈ nthL da1 x, c / 2 < 3 := by decide +kernel
theorem letters_da2 : ∀ x < 5, ∀ c ∈ nthL da2 x, c / 2 < 3 := by decide +kernel

theorem para1 (hC : ChevFacts) :
    Para EQ1.CF EA1.CF wQ1 wA1 (bN 1) pcB1 aM1 dq1 da1 nm1 dj1 pc1Y A1gen (nY 1) M1 :=
  { parts := paraParts ch733008_para1
    rQ := rQ1 hC
    rA := rA1 hC
    lenQ := rfl
    lenA := rfl
    hSQ := fun _ => rfl
    hSA := fun t => by fin_cases t <;> rfl
    hn := psi_nY hC 1
    hn2 := gensParts.n1
    hBM := hC.B0_le_M1
    hnM := hC.nY_one_mem_M1
    hMle := hC.M1_le_of
    bA := letters_aM1
    bq := letters_dq1
    ba := letters_da1 }

theorem para2 (hC : ChevFacts) :
    Para EQ2.CF EA2.CF wQ2 wA2 (bN 0) pcB2 aM2 dq2 da2 nm2 dj2 pc2Y A2gen (nY 0) M2 :=
  { parts := paraParts ch733008_para2
    rQ := rQ2 hC
    rA := rA2 hC
    lenQ := rfl
    lenA := rfl
    hSQ := fun _ => rfl
    hSA := fun t => by fin_cases t <;> rfl
    hn := psi_nY hC 0
    hn2 := gensParts.n0
    hBM := hC.B0_le_M2
    hnM := hC.nY_zero_mem_M2
    hMle := hC.M2_le_of
    bA := letters_aM2
    bq := letters_dq2
    ba := letters_da2 }

theorem Q1_le_T0' (hC : ChevFacts) : Q1 ≤ T0 :=
  hC.le_T0_of_isPGroup ((Q1_le_closure hC).trans (closure_le_B0 hC))
    (isPGroup_of_card_two_pow (k := 10) (card_Q1' hC))

theorem Q2_le_T0' (hC : ChevFacts) : Q2 ≤ T0 :=
  hC.le_T0_of_isPGroup ((Q2_le_closure hC).trans (closure_le_B0 hC))
    (isPGroup_of_card_two_pow (k := 10) (card_Q2' hC))

theorem H0_le_B0' (hC : ChevFacts) : CFSG.Quasithin.F112R.St84.G24M.H0 ≤ B0 := by
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rcases hx with rfl | rfl
  · rw [← gB0_0]
    exact gB0_mem_B0' hC 0
  · rw [← gB0_1]
    exact gB0_mem_B0' hC 1

theorem borelFacts (hC : ChevFacts) : BorelFacts where
  toGL_gB0 := toGL_gB0' hC
  gB0_mem_B0 := gB0_mem_B0' hC
  closure_gB0 := closure_gB0' hC
  orderOf_k1Y := orderOf_k1Y' hC
  orderOf_k2Y := orderOf_k2Y' hC
  orderOf_xaY := orderOf_xaY' hC
  orderOf_xbY := orderOf_xbY' hC
  commute_k1Y_k2Y := commute_k1Y_k2Y' hC
  commute_k1Y_xaY := commute_k1Y_xaY' hC
  commute_k2Y_xbY := commute_k2Y_xbY' hC
  H0_le_B0 := H0_le_B0' hC
  card_H0 := card_H0' hC
  card_Q1 := card_Q1' hC
  card_Q2 := card_Q2' hC
  card_A1 := card_A1' hC
  card_A2 := card_A2' hC
  Q1_le_T0 := Q1_le_T0' hC
  Q2_le_T0 := Q2_le_T0' hC
  A1_le_M1 := para_A_le hC (para1 hC)
  A2_le_M2 := para_A_le hC (para2 hC)
  sup_Q1_A1 := para_sup hC (para1 hC) (Q1_le_closure hC)
  sup_Q2_A2 := para_sup hC (para2 hC) (Q2_le_closure hC)
  inf_A1_Q1 := para_inf hC (para1 hC)
  inf_A2_Q2 := para_inf hC (para2 hC)
  M1_le_normalizer_Q1 := para_normalizer hC (para1 hC)
  M2_le_normalizer_Q2 := para_normalizer hC (para2 hC)
  pCoreOf_M1 := para_pCore hC (para1 hC) (Q1_le_closure hC) hC.card_pCoreOf_M1
  pCoreOf_M2 := para_pCore hC (para2 hC) (Q2_le_closure hC) hC.card_pCoreOf_M2

end CFSG.KD.G24B
