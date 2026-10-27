module

public import Certificates.Kernel.SporCovLane.HNWit
public import Certificates.Kernel.HNF26720.Facts
public import CFSG.Certificates.Kernel.SporCov.ChainKit
public import CFSG.Sporadic.HNSchreier.FALocal
import Certificates.Kernel.HN3166.Seed
import CFSG.Certificates.Kernel.Fam.HNSeed.Checks.K
import Mathlib

public section

namespace CFSG.KD.SporCovLane.HNWit

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.Sporadic.HNSchreier
open CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier CertificateChecks.KernelHNF26720

section Words

variable {G : Type} [Group G] (a b : G)

def PairOK (E : List G) (q : ℕ × ℕ) (g : G) : Prop :=
  q.1 < 4 + E.length ∧ q.2 < 4 + E.length ∧ letG a b E q.1 = g ∧ letG a b E q.2 = g⁻¹

theorem letG_append {E : List G} {c : ℕ} (F : List G) (hc : c < 4 + E.length) :
    letG a b (E ++ F) c = letG a b E c := by
  unfold letG
  split_ifs with h
  · rfl
  · exact List.getD_append _ _ _ _ (by omega)

theorem PairOK.mono {E : List G} {q : ℕ × ℕ} {g : G} (F : List G) (h : PairOK a b E q g) :
    PairOK a b (E ++ F) q g := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · rw [List.length_append]
    omega
  · rw [letG_append a b F h1, h3]
  · rw [letG_append a b F h2, h4]

theorem regsG_append : ∀ (W₁ W₂ : List (List ℕ)) (E : List G),
    regsG a b (W₁ ++ W₂) E = regsG a b W₂ (regsG a b W₁ E)
  | [], _, _ => rfl
  | w :: W₁, W₂, E => regsG_append W₁ W₂ (E ++ [wE (letG a b E) w])

theorem regsG_length : ∀ (W : List (List ℕ)) (E : List G),
    (regsG a b W E).length = E.length + W.length
  | [], E => rfl
  | w :: W, E => by
    simp only [regsG_cons, regsG_length W, List.length_append, List.length_cons, List.length_nil]
    omega

theorem letG_new (E : List G) (x y : G) :
    letG a b (E ++ [x] ++ [y]) (4 + E.length) = x ∧
      letG a b (E ++ [x] ++ [y]) (5 + E.length) = y := by
  unfold letG
  rw [if_neg (by omega), if_neg (by omega), List.append_assoc, List.singleton_append,
    List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
  have e1 : 4 + E.length - 4 - E.length = 0 := by omega
  have e2 : 5 + E.length - 4 - E.length = 1 := by omega
  rw [e1, e2]
  exact ⟨rfl, rfl⟩

@[expose] def sprod (hv : ℕ → G) (w : List ℤ) : G :=
  (w.map fun l => if 0 < l then hv (l.natAbs - 1) else (hv (l.natAbs - 1))⁻¹).prod

theorem wE_kwS {E : List G} {H : ℕ → ℕ × ℕ} {hv : ℕ → G} :
    ∀ w : List ℤ, (∀ l ∈ w, PairOK a b E (H (l.natAbs - 1)) (hv (l.natAbs - 1))) →
      wE (letG a b E) (kwS H w) = sprod hv w ∧ wE (letG a b E) (kwSi H w) = (sprod hv w)⁻¹
  | [], _ => ⟨rfl, by rw [sprod, List.map_nil, List.prod_nil, inv_one]; rfl⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := wE_kwS w fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    obtain ⟨-, -, h3, h4⟩ := h l List.mem_cons_self
    have hs : sprod hv (l :: w) =
        (if 0 < l then hv (l.natAbs - 1) else (hv (l.natAbs - 1))⁻¹) * sprod hv w := by
      rw [sprod, List.map_cons, List.prod_cons]
      rfl
    refine ⟨?_, ?_⟩
    · rw [kwS, List.map_cons, List.reverse_cons, wE_append, ← kwS, ih1, wE_cons, wE_nil, one_mul,
        hs, sgnL]
      split_ifs <;> simp_all
    · rw [kwSi, List.map_cons, wE_cons, ← kwSi, ih2, hs, mul_inv_rev, sgnLi]
      split_ifs <;> simp_all

theorem prog_pairs : ∀ (prog : List (ℕ × ℕ × ℕ)) (σ : ℕ → ℕ × ℕ) (R : ℕ → G) (E : List G),
    (∀ r, PairOK a b E (σ r) (R r)) →
      ∀ r, PairOK a b (regsG a b (progW σ E.length prog) E) (progP σ E.length prog r)
        (runProg R prog r)
  | [], σ, R, E, h => h
  | (x, y, c) :: rest, σ, R, E, h => by
    have hx := h x
    have hy := h y
    set g := R x * R y
    have e1 : wE (letG a b E) [(σ y).1, (σ x).1] = g := by
      rw [wE_cons, wE_cons, wE_nil, one_mul, hx.2.2.1, hy.2.2.1]
    set E1 := E ++ [wE (letG a b E) [(σ y).1, (σ x).1]]
    have e2 : wE (letG a b E1) [(σ x).2, (σ y).2] = g⁻¹ := by
      rw [wE_cons, wE_cons, wE_nil, one_mul, letG_append a b _ hx.2.1, letG_append a b _ hy.2.1,
        hx.2.2.2, hy.2.2.2, mul_inv_rev]
    set E2 := E1 ++ [wE (letG a b E1) [(σ x).2, (σ y).2]]
    have hl1 : E1.length = E.length + 1 := by simp [E1]
    have hl2 : E2.length = E.length + 2 := by simp [E2, hl1]
    have hreg : regsG a b (progW σ E.length ((x, y, c) :: rest)) E =
        regsG a b (progW (upd σ c (4 + E.length, 5 + E.length)) E2.length rest) E2 := by
      rw [hl2]
      rfl
    have hP : progP σ E.length ((x, y, c) :: rest) =
        progP (upd σ c (4 + E.length, 5 + E.length)) E2.length rest := by
      rw [hl2]
      rfl
    have hR : runProg R ((x, y, c) :: rest) = runProg (Function.update R c g) rest := rfl
    rw [hreg, hP, hR]
    refine prog_pairs rest _ _ E2 fun r => ?_
    by_cases hr : r = c
    · subst hr
      rw [Function.update_self]
      have hu : upd σ r (4 + E.length, 5 + E.length) r = (4 + E.length, 5 + E.length) := by
        simp [upd]
      rw [hu]
      obtain ⟨n1, n2⟩ := letG_new a b E (wE (letG a b E) [(σ y).1, (σ x).1])
        (wE (letG a b E1) [(σ x).2, (σ y).2])
      refine ⟨?_, ?_, n1.trans e1, n2.trans e2⟩
      · change 4 + E.length < 4 + E2.length
        omega
      · change 5 + E.length < 4 + E2.length
        omega
    · rw [Function.update_of_ne hr]
      have hu : upd σ c (4 + E.length, 5 + E.length) r = σ r := by simp [upd, hr]
      rw [hu]
      have := ((h r).mono a b [wE (letG a b E) [(σ y).1, (σ x).1]]).mono a b
        [wE (letG a b E1) [(σ x).2, (σ y).2]]
      exact this

theorem strong_pairs (hv : ℕ → G) : ∀ (ws : List (List ℤ)) (H : ℕ → ℕ × ℕ) (j : ℕ) (E : List G),
    (∀ i < j, PairOK a b E (H i) (hv i)) →
    (∀ m (hm : m < ws.length), hv (j + m) = sprod hv ws[m] ∧
      ∀ l ∈ ws[m], l ≠ 0 ∧ l.natAbs ≤ j + m) →
      ∀ i < j + ws.length, PairOK a b (regsG a b (strongW H j E.length ws) E)
        (strongP H j E.length ws i) (hv i)
  | [], H, j, E, h, _ => fun i hi => h i (by simpa using hi)
  | w :: rest, H, j, E, h, hw => by
    obtain ⟨hw0, hl0⟩ := hw 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at hw0 hl0
    have hlet : ∀ l ∈ w, PairOK a b E (H (l.natAbs - 1)) (hv (l.natAbs - 1)) := fun l hl =>
      h _ (by have := hl0 l hl; omega)
    obtain ⟨k1, -⟩ := wE_kwS a b w hlet
    set E1 := E ++ [wE (letG a b E) (kwS H w)]
    obtain ⟨-, k2⟩ := wE_kwS a b w fun l hl => (hlet l hl).mono a b
      [wE (letG a b E) (kwS H w)]
    set E2 := E1 ++ [wE (letG a b E1) (kwSi H w)]
    have hl1 : E1.length = E.length + 1 := by simp [E1]
    have hl2 : E2.length = E.length + 2 := by simp [E2, hl1]
    have hreg : regsG a b (strongW H j E.length (w :: rest)) E =
        regsG a b (strongW (upd H j (4 + E.length, 5 + E.length)) (j + 1) E2.length rest) E2 := by
      rw [hl2]
      rfl
    have hP : strongP H j E.length (w :: rest) =
        strongP (upd H j (4 + E.length, 5 + E.length)) (j + 1) E2.length rest := by
      rw [hl2]
      rfl
    intro i hi
    rw [hreg, hP]
    refine strong_pairs hv rest _ (j + 1) E2 (fun i' hi' => ?_) (fun m hm => ?_) i
      (by simp at hi; omega)
    · by_cases hj : i' = j
      · subst hj
        have hu : upd H i' (4 + E.length, 5 + E.length) i' = (4 + E.length, 5 + E.length) := by
          simp [upd]
        rw [hu]
        obtain ⟨n1, n2⟩ := letG_new a b E (wE (letG a b E) (kwS H w))
          (wE (letG a b E1) (kwSi H w))
        refine ⟨?_, ?_, n1.trans (k1.trans hw0.symm), n2.trans (by rw [k2, hw0])⟩
        · change 4 + E.length < 4 + E2.length
          omega
        · change 5 + E.length < 4 + E2.length
          omega
      · have hu : upd H j (4 + E.length, 5 + E.length) i' = H i' := by simp [upd, hj]
        rw [hu]
        exact ((h i' (by omega)).mono a b _).mono a b _
    · obtain ⟨e, hl⟩ := hw (m + 1) (by simp; omega)
      have e' : j + 1 + m = j + (m + 1) := by omega
      refine ⟨by rw [e', e, List.getElem_cons_succ], fun l hl' => ?_⟩
      have := hl l (by simpa using hl')
      omega

theorem evalWord_pto (g : ℕ → G) (k : ℕ) : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ k) →
    Quiver.SchreierGraph.evalWord (fun h : Fin k => g h.val) (ptoLetters k w) = sprod g w
  | [], _ => rfl
  | l :: w, hl => by
    have hl0 := hl l List.mem_cons_self
    have hcons : ptoLetters k (l :: w) = (⟨l.natAbs - 1, by omega⟩, decide (0 < l)) ::
        ptoLetters k w := by
      simp [ptoLetters, hl0.1, hl0.2]
    have hs : sprod g (l :: w) =
        (if 0 < l then g (l.natAbs - 1) else (g (l.natAbs - 1))⁻¹) * sprod g w := by
      rw [sprod, List.map_cons, List.prod_cons]
      rfl
    rw [hcons, hs, ← evalWord_pto g k w fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')]
    by_cases hpos : 0 < l
    · rw [decide_eq_true hpos, Quiver.SchreierGraph.evalWord_cons_true, if_pos hpos]
    · have hd : decide (0 < l) = false := by simpa using hpos
      rw [hd, Quiver.SchreierGraph.evalWord_cons_false, if_neg hpos]

theorem wE_six (f : ℕ → G) (c : ℕ) : wE f [c, c, c, c, c, c] = f c ^ 6 := by
  simp only [wE_cons, wE_nil, one_mul, pow_succ, pow_zero]

theorem wE_repW (f : ℕ → G) (w : List ℕ) : ∀ p, wE f (repW w p) = wE f w ^ p
  | 0 => by
    rw [pow_zero]
    rfl
  | p + 1 => by
    change wE f (w ++ repW w p) = _
    rw [wE_append, wE_repW f w p, pow_succ]

end Words

theorem sw_length : sw.length = 15 := by decide +kernel

theorem hJ_succ (m : ℕ) (hm : m < sw.length) :
    hJ (2 + m) = sprod hJ sw[m] ∧ ∀ l ∈ sw[m], l ≠ 0 ∧ l.natAbs ≤ 2 + m := by
  have hm15 : m < 15 := by
    rw [sw_length] at hm
    exact hm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hsz, -, -, hw, -⟩ := local_parts_data
  have hsw : sw[m] = LocalData.strongWords[2 + m]! := by
    simp [sw, getElem!_pos LocalData.strongWords (2 + m) (by rw [hsz]; omega)]
  have hl := hw (2 + m) (by omega) (by omega)
  have key : hJ (2 + m) = sprod hJ LocalData.strongWords[2 + m]! ∧
      ∀ l ∈ LocalData.strongWords[2 + m]!, l ≠ 0 ∧ l.natAbs ≤ 2 + m := by
    refine ⟨?_, hl⟩
    rw [hJ, gStrong_of_ge _ _ (by simp)]
    exact evalWord_pto _ _ _ hl
  rw [← hsw] at key
  exact key

theorem c3_letters : ∀ l ∈ FAData.c3Words[0]!, l ≠ 0 ∧ l.natAbs ≤ 17 := by decide +kernel

theorem g3H_letters : ∀ l ∈ FAData.g3H, l ≠ 0 ∧ l.natAbs ≤ 17 := by decide +kernel

theorem progW_length : (progW pInit 1 Data.subgroupProgram).length = 20 := by decide +kernel

noncomputable abbrev E2 : List ↥JH :=
  regsG aJ bJ (strongW H0 2 21 sw) (regsG aJ bJ (progW pInit 1 Data.subgroupProgram)
    (regsG aJ bJ [[]] []))

theorem strongW_length : (strongW H0 2 21 sw).length = 30 := by decide +kernel

theorem E2_length : E2.length = 51 := by
  rw [regsG_length, regsG_length, regsG_length, progW_length, strongW_length]
  rfl

theorem strong_pairs_J : ∀ i < 17, PairOK aJ bJ E2 (Hp i) (hJ i) := by
  have h0 : ∀ r, PairOK aJ bJ (regsG aJ bJ [[]] []) (pInit r) (jRegs0 r) := by
    intro r
    unfold pInit jRegs0
    split_ifs <;> refine ⟨by simp [regsG], by simp [regsG], ?_, ?_⟩ <;>
      simp [letG, f4, regsG, wE_nil]
  have h1 := prog_pairs aJ bJ Data.subgroupProgram pInit jRegs0 _ h0
  have hl0 : (regsG aJ bJ [[]] ([] : List ↥JH)).length = 1 := rfl
  rw [hl0] at h1
  have hlen1 : (regsG aJ bJ (progW pInit 1 Data.subgroupProgram) (regsG aJ bJ [[]] [])).length =
      21 := by
    rw [regsG_length, progW_length]
    rfl
  have hb : ∀ i < 2, PairOK aJ bJ
      (regsG aJ bJ (progW pInit 1 Data.subgroupProgram) (regsG aJ bJ [[]] [])) (H0 i) (hJ i) := by
    intro i hi
    interval_cases i
    · have e : hJ 0 = jRegs 1 := gStrong_of_lt _ _ (by simp)
      have e' : H0 0 = Pp 1 := rfl
      rw [e, e']
      exact h1 1
    · have e : hJ 1 = jRegs 2 := gStrong_of_lt _ _ (by simp)
      have e' : H0 1 = Pp 2 := rfl
      rw [e, e']
      exact h1 2
  have h2 := strong_pairs aJ bJ hJ sw H0 2 _ hb hJ_succ
  rw [hlen1, sw_length] at h2
  exact h2

theorem hWordJ_eq (w : List ℤ) : hWordJ w = sprod hJ w := rfl

theorem c3J_zero : c3J 0 = hWordJ FAData.c3Words[0]! := by
  rw [c3J, if_pos (by norm_num)]

theorem reg_c : wE (letG aJ bJ E2) (kwS Hp FAData.c3Words[0]!) = c3J 0 := by
  rw [c3J_zero, hWordJ_eq]
  exact (wE_kwS aJ bJ FAData.c3Words[0]! fun l hl =>
    strong_pairs_J _ (by have := c3_letters l hl; omega)).1

theorem seedWordJ_cons (l : ℕ) (w : List ℕ) :
    seedWordJ (l :: w) = (if l = 1 then aJ else bJ) * seedWordJ w := by
  rw [seedWordJ, seedWordJ, List.map_cons, List.prod_cons]

theorem wE_seedJ (E : List ↥JH) : ∀ w : List ℕ,
    wE (letG aJ bJ E) ((w.map fun l => if l = 1 then 0 else 2).reverse) = seedWordJ w
  | [] => by
    rw [seedWordJ, List.map_nil, List.map_nil, List.prod_nil, List.reverse_nil, wE_nil]
  | l :: w => by
    rw [List.map_cons, List.reverse_cons, wE_append, wE_seedJ E w, wE_cons, wE_nil, one_mul,
      seedWordJ_cons]
    congr 1
    by_cases h : l = 1 <;> simp [h, letG, f4]

theorem g3W_split (E : List ↥JH) :
    wE (letG aJ bJ E) g3W = seedWordJ FAData.g3Root * wE (letG aJ bJ E) (kwS Hp FAData.g3H) := by
  rw [g3W, wE_append, wE_seedJ]

theorem reg_h (x : ↥JH) : wE (letG aJ bJ (E2 ++ [x])) (kwS Hp FAData.g3H) = hWordJ FAData.g3H := by
  rw [hWordJ_eq]
  exact (wE_kwS aJ bJ FAData.g3H fun l hl =>
    (strong_pairs_J _ (by have := g3H_letters l hl; omega)).mono aJ bJ [x]).1

theorem reg_g (x : ↥JH) : wE (letG aJ bJ (E2 ++ [x])) g3W = g3J := by
  rw [g3W_split, reg_h, g3J]

theorem reg_u (x y : ↥JH) :
    wE (letG aJ bJ (E2 ++ [x] ++ [y])) [56, 56, 56, 56, 56, 56] = y ^ 6 := by
  rw [wE_six]
  have e := (letG_new aJ bJ E2 x y).2
  rw [E2_length] at e
  rw [e]

theorem regs_eq : regsG aJ bJ Ws [] = E2 ++ [c3J 0] ++ [g3J] ++ [g3J ^ 6] := by
  have hW : regsG aJ bJ Ws [] =
      regsG aJ bJ [kwS Hp FAData.c3Words[0]!, g3W, [56, 56, 56, 56, 56, 56]] E2 := by
    rw [Ws, regsG_append, regsG_append, regsG_append]
  rw [hW, regsG_cons, regsG_cons, regsG_cons, regsG_nil, reg_c, reg_g, reg_u]

theorem fC_C : fC aJ bJ Ws C = c3J 0 := by
  rw [fC, regs_eq]
  have e := (letG_new aJ bJ E2 (c3J 0) g3J).1
  rw [E2_length] at e
  rw [letG_append aJ bJ _ (by rw [List.length_append, List.length_append, E2_length]; decide), e]

theorem fC_U : fC aJ bJ Ws U = g3J ^ 6 := by
  rw [fC, regs_eq]
  have e := (letG_new aJ bJ (E2 ++ [c3J 0]) g3J (g3J ^ 6)).2
  rw [List.length_append, E2_length] at e
  exact e

theorem hn_witness : (g3J ^ 6) ^ 5 = 1 ∧ g3J ^ 6 ≠ 1 ∧
    ∀ j < 4, c3J 0 * g3J ^ 6 ≠ (g3J ^ 6) ^ (j + 1) * c3J 0 := by
  have vB := CertificateChecks.KernelHN.s_v2
  have vBi := (CFSG.KS.J4Hub.mul_sound' (hnb := rfl) CFSG.KD.FamHNSeed.consts vB vB).1
  have hA : ordMat 5 133 13 1729 (CFSG.KD.FamHNSeed.RW 1) = ρJ aJ :=
    ((ρJ_apply aJ).trans matJ_aJ).symm
  have hB : ordMat 5 133 13 1729 (CFSG.KD.FamHNSeed.RW 2) = ρJ bJ :=
    ((ρJ_apply bJ).trans matJ_bJ).symm
  have hok := Ck.ok
  unfold kit at hok
  obtain ⟨mw, hk, hmw⟩ := kitC_sound CFSG.KD.FamHNSeed.consts (nb := 229957) rfl
    CertificateChecks.KernelHN.s_v1 CertificateChecks.KernelHN.s_v1 vB vBi hA hB hok
  set ev := wE (fC aJ bJ Ws) with hev
  have sound : ∀ u v, eqM mw u v = true → ev u = ev v := by
    intro u v h
    apply ρJ_injective
    rw [← (hmw u).2, ← (hmw v).2, Nat.eq_of_beq_eq_true h]
  have compl : ∀ u v, ev u = ev v → eqM mw u v = true := by
    intro u v h
    unfold eqM
    rw [CFSG.KS.J4Hub.ordMat_inj' CFSG.KD.FamHNSeed.consts rfl (hmw u).1 (hmw v).1
      (by rw [(hmw u).2, (hmw v).2, h])]
    exact Nat.beq_refl _
  have eU : ev [U] = g3J ^ 6 := by rw [hev, wE_cons, wE_nil, one_mul, fC_U]
  have eUC : ev [U, C] = c3J 0 * g3J ^ 6 := by
    rw [hev, wE_cons, wE_cons, wE_nil, one_mul, fC_U, fC_C]
  have eCU : ∀ j, ev (C :: repW [U] (j + 1)) = (g3J ^ 6) ^ (j + 1) * c3J 0 := by
    intro j
    rw [hev, wE_cons, wE_repW, ← hev, eU, fC_C]
  unfold chk neq at hk
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk
  obtain ⟨⟨⟨⟨⟨h5, h1⟩, n0⟩, n1⟩, n2⟩, n3⟩ := hk
  refine ⟨?_, fun h => ?_, fun j hj h => ?_⟩
  · have e := sound _ _ h5
    rw [hev, wE_repW, ← hev, eU] at e
    exact e
  · have e := compl [U] [] (by rw [eU, h]; rfl)
    rw [e] at h1
    exact absurd h1 (by decide)
  · have e := compl [U, C] (C :: repW [U] (j + 1)) (by rw [eUC, eCU, h])
    interval_cases j
    · rw [e] at n0
      exact absurd n0 (by decide)
    · rw [e] at n1
      exact absurd n1 (by decide)
    · rw [e] at n2
      exact absurd n2 (by decide)
    · rw [e] at n3
      exact absurd n3 (by decide)

end CFSG.KD.SporCovLane.HNWit

end
