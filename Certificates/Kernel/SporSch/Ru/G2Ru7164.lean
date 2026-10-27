module

public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public meta import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public import Certificates.Kernel.SporSch.Ru.G2Ru7164K
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Monster.B.Co2.PermArr
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.G2Ru7164

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSporSch.RuG
  CFSG.Quasithin.H13.Ch4.G2Ru CFSG.KC.BfsPin CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

abbrev P (p : Nat) : Prop := PP 4060 12 p

theorem hsz : szOK 4060 12 = true := by decide

theorem P_pc {a b : Nat} (ha : P a) (hb : P b) : P (pc a b) := ha.mul hb
theorem P_pinv {a : Nat} (ha : P a) : P (pinv a) := ha.inv
theorem P_pid : P pid := PP.id hsz

theorem comp_eq {a b : Nat} (ha : P a) (hb : P b) :
    compA 4060 (unpack 4060 12 a) (unpack 4060 12 b) = unpack 4060 12 (pc a b) := compA_PP ha hb

theorem inv_eq {a : Nat} (ha : P a) : invCand 4060 (unpack 4060 12 a) = unpack 4060 12 (pinv a) :=
  invCand_PP ha

theorem id_eq : idA 4060 = unpack 4060 12 pid := idA_eq hsz

theorem eq_eq {a b : Nat} (ha : P a) (hb : P b) :
    eqA 4060 (unpack 4060 12 a) (unpack 4060 12 b) = Nat.beq a b := eqA_PP ha hb

theorem perms : P C0 ∧ P C1 ∧ ∀ j < 4, P (SG j) := by
  have h := kPerm
  simp only [bAnd_iff, List.all_eq_true, List.mem_range] at h
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨PP_of_permOK hsz h0, PP_of_permOK hsz h1, fun j hj => PP_of_permOK hsz (h2 j hj)⟩

theorem wordA_eq {S : Array (Array Nat)} {k : Nat} {G : Nat → Nat} (hs : S.size = k)
    (hS : ∀ j < k, S[j]! = unpack 4060 12 (G j)) (hP : ∀ j < k, P (G j)) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ k) →
      wordA 4060 S (S.map (invCand 4060)) w = unpack 4060 12 (wK G w) ∧ P (wK G w)
  | [], _ => ⟨id_eq, P_pid⟩
  | l :: w, h => by
    obtain ⟨ih1, ih2⟩ := wordA_eq hs hS hP w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨hl0, hlk⟩ := h l List.mem_cons_self
    have hlet : letterA S (S.map (invCand 4060)) l = unpack 4060 12 (letK G l) ∧ P (letK G l) := by
      unfold letterA letK
      by_cases hpos : 0 < l
      · have hj : l.toNat - 1 < k := by omega
        rw [if_pos hpos, decide_eq_true hpos]
        exact ⟨hS _ hj, hP _ hj⟩
      · have hj : (-l).toNat - 1 < k := by omega
        rw [if_neg hpos, decide_eq_false hpos, getElem!_pos _ _ (by rw [Array.size_map]; omega),
          Array.getElem_map, ← getElem!_pos S _ (by omega), hS _ hj]
        exact ⟨inv_eq (hP _ hj), P_pinv (hP _ hj)⟩
    have e : wordA 4060 S (S.map (invCand 4060)) (l :: w) =
        compA 4060 (letterA S (S.map (invCand 4060)) l) (wordA 4060 S (S.map (invCand 4060)) w) := rfl
    rw [e, hlet.1, ih1, comp_eq hlet.2 ih2]
    exact ⟨rfl, P_pc hlet.2 ih2⟩

theorem sg_binds : ruSGensA.size = 4 ∧ ∀ j < 4, ruSGensA[j]! = unpack 4060 12 (SG j) :=
  ⟨by simp [ruSGensA, ruSWords], fun _ hj => sg_eq hj⟩

theorem sw_eq {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 4) :
    g2SW w = unpack 4060 12 (wK SG w) ∧ P (wK SG w) :=
  wordA_eq sg_binds.1 sg_binds.2 perms.2.2 w hw

theorem cw_eq {w : List Int} (hw : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) :
    CFSG.Quasithin.H13.KGRu.ruCW w = unpack 4060 12 (wK Cf w) ∧ P (wK Cf w) := by
  have hb : ∀ j < 2, (#[ruC0A, ruC1A] : Array (Array Nat))[j]! = unpack 4060 12 (Cf j) := by
    intro j hj
    interval_cases j
    · exact c0_eq
    · exact c1_eq
  have hP : ∀ j < 2, P (Cf j) := by
    intro j hj
    interval_cases j
    · exact perms.1
    · exact perms.2.1
  have e : CFSG.Quasithin.H13.KGRu.ruCW w =
      wordA 4060 #[ruC0A, ruC1A] (Array.map (invCand 4060) #[ruC0A, ruC1A]) w := by
    unfold CFSG.Quasithin.H13.KGRu.ruCW
    simp [ruInv]
  rw [e]
  exact wordA_eq (by rfl) hb hP w hw

theorem wg_eq {k : Nat} (hk : k < 6) : g2WGenA[k]! = unpack 4060 12 (WG k) ∧ P (WG k) := by
  have e : g2WGenA[k]! = g2SW (g2WWords.getD k []) := by
    interval_cases k <;> rfl
  rw [e]
  interval_cases k
  · exact sw_eq (w := g2WWords.getD 0 []) (by decide)
  · exact sw_eq (w := g2WWords.getD 1 []) (by decide)
  · exact sw_eq (w := g2WWords.getD 2 []) (by decide)
  · exact sw_eq (w := g2WWords.getD 3 []) (by decide)
  · exact sw_eq (w := g2WWords.getD 4 []) (by decide)
  · exact sw_eq (w := g2WWords.getD 5 []) (by decide)

theorem vg_eq {k : Nat} (hk : k < 3) : g2VGenA[k]! = unpack 4060 12 (VG k) ∧ P (VG k) := by
  interval_cases k
  · have e : g2VGenA[0]! = g2WGenA[0]! := by
      unfold g2VGenA
      simp
    rw [e]
    exact wg_eq (by norm_num)
  · have e : g2VGenA[1]! = g2SW (g2VWords.getD 0 []) := by
      unfold g2VGenA
      simp
    rw [e]
    exact sw_eq (w := g2VWords.getD 0 []) (by decide)
  · have e : g2VGenA[2]! = g2SW (g2VWords.getD 1 []) := by
      unfold g2VGenA
      simp
    rw [e]
    exact sw_eq (w := g2VWords.getD 1 []) (by decide)

theorem powA_eq {t : Nat} (ht : P t) :
    ∀ e, powA 4060 (unpack 4060 12 t) e = unpack 4060 12 (powK t e) ∧ P (powK t e)
  | 0 => ⟨id_eq, P_pid⟩
  | e + 1 => by
    obtain ⟨ih1, ih2⟩ := powA_eq ht e
    have e1 : powA 4060 (unpack 4060 12 t) (e + 1) = compA 4060 (unpack 4060 12 t)
        (powA 4060 (unpack 4060 12 t) e) := rfl
    rw [e1, ih1, comp_eq ht ih2]
    exact ⟨rfl, P_pc ht ih2⟩

theorem conj_eq {t u : Nat} (ht : P t) (hu : P u) :
    compA 4060 (compA 4060 (unpack 4060 12 t) (unpack 4060 12 u)) (invCand 4060 (unpack 4060 12 t)) =
      unpack 4060 12 (conjK t u) ∧ P (conjK t u) := by
  rw [comp_eq ht hu, inv_eq ht, comp_eq (P_pc ht hu) (P_pinv ht)]
  exact ⟨rfl, P_pc (P_pc ht hu) (P_pinv ht)⟩

theorem prod3 {a b c : Nat} (ha : P a) (hb : P b) (hc : P c) (e : Nat) :
    compA 4060 (powA 4060 (unpack 4060 12 a) (e % 2)) (compA 4060
      (powA 4060 (unpack 4060 12 b) (e / 2 % 2)) (powA 4060 (unpack 4060 12 c) (e / 4 % 2))) =
      unpack 4060 12 (pc (powK a (e % 2)) (pc (powK b (e / 2 % 2)) (powK c (e / 4 % 2)))) ∧
    P (pc (powK a (e % 2)) (pc (powK b (e / 2 % 2)) (powK c (e / 4 % 2)))) := by
  obtain ⟨a1, a2⟩ := powA_eq ha (e % 2)
  obtain ⟨b1, b2⟩ := powA_eq hb (e / 2 % 2)
  obtain ⟨c1, c2⟩ := powA_eq hc (e / 4 % 2)
  rw [a1, b1, c1, comp_eq b2 c2, comp_eq a2 (P_pc b2 c2)]
  exact ⟨rfl, P_pc a2 (P_pc b2 c2)⟩

theorem wprod_eq (e : Nat) : g2WProd e = unpack 4060 12 (WPk e) ∧ P (WPk e) := by
  obtain ⟨w0, p0⟩ := wg_eq (k := 0) (by norm_num)
  obtain ⟨w1, p1⟩ := wg_eq (k := 1) (by norm_num)
  obtain ⟨w2, p2⟩ := wg_eq (k := 2) (by norm_num)
  obtain ⟨w3, p3⟩ := wg_eq (k := 3) (by norm_num)
  obtain ⟨w4, p4⟩ := wg_eq (k := 4) (by norm_num)
  obtain ⟨w5, p5⟩ := wg_eq (k := 5) (by norm_num)
  obtain ⟨a0, q0⟩ := powA_eq p0 (e % 2)
  obtain ⟨a1, q1⟩ := powA_eq p1 (e / 2 % 2)
  obtain ⟨a2, q2⟩ := powA_eq p2 (e / 4 % 2)
  obtain ⟨a3, q3⟩ := powA_eq p3 (e / 8 % 2)
  obtain ⟨a4, q4⟩ := powA_eq p4 (e / 16 % 2)
  obtain ⟨a5, q5⟩ := powA_eq p5 (e / 32 % 2)
  unfold g2WProd
  rw [w0, w1, w2, w3, w4, w5, a0, a1, a2, a3, a4, a5, comp_eq q4 q5, comp_eq q3 (P_pc q4 q5),
    comp_eq q2 (P_pc q3 (P_pc q4 q5)), comp_eq q1 (P_pc q2 (P_pc q3 (P_pc q4 q5))),
    comp_eq q0 (P_pc q1 (P_pc q2 (P_pc q3 (P_pc q4 q5))))]
  exact ⟨rfl, P_pc q0 (P_pc q1 (P_pc q2 (P_pc q3 (P_pc q4 q5))))⟩

theorem vprod_eq (e : Nat) : g2VProd e = unpack 4060 12 (VPk e) ∧ P (VPk e) := by
  obtain ⟨v0, p0⟩ := vg_eq (k := 0) (by norm_num)
  obtain ⟨v1, p1⟩ := vg_eq (k := 1) (by norm_num)
  obtain ⟨v2, p2⟩ := vg_eq (k := 2) (by norm_num)
  unfold g2VProd
  rw [v0, v1, v2]
  exact prod3 p0 p1 p2 e

theorem any_ofFn {m : Nat} (f : Fin m → Array Nat) (p : Array Nat → Bool) :
    (Array.ofFn f).any p = (List.range m).any fun e => if h : e < m then p (f ⟨e, h⟩) else false := by
  rw [Bool.eq_iff_iff, Array.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [Array.size_ofFn] at hi
    refine ⟨i, List.mem_range.2 hi, ?_⟩
    rw [dif_pos hi]
    simpa using h
  · rintro ⟨i, hi, h⟩
    have hi' := List.mem_range.1 hi
    rw [dif_pos hi'] at h
    exact ⟨i, by simpa using hi', by simpa using h⟩

theorem any_congr_mem {l : List Nat} {f g : Nat → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem inW_eq {T : Nat} (hT : P T) : g2InW (unpack 4060 12 T) = inWK T := by
  unfold g2InW g2WArr inWK
  rw [any_ofFn]
  apply any_congr_mem
  intro e he
  have he' := List.mem_range.1 he
  rw [dif_pos he', (wprod_eq e).1, eq_eq hT (wprod_eq e).2]

theorem inV_eq {T : Nat} (hT : P T) : g2InV (unpack 4060 12 T) = inVK T := by
  unfold g2InV g2VArr inVK
  rw [any_ofFn]
  apply any_congr_mem
  intro e he
  have he' := List.mem_range.1 he
  rw [dif_pos he', (vprod_eq e).1, eq_eq hT (vprod_eq e).2]

theorem allLt_eq {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allLt n f = (List.range n).all g := by
  rw [Bool.eq_iff_iff, CFSG.Monster.B.Co2.allLt_iff, List.all_eq_true]
  constructor
  · intro H x hx
    have hx' := List.mem_range.1 hx
    rw [← h x hx']
    exact H x hx'
  · intro H i hi
    rw [h i hi]
    exact H i (List.mem_range.2 hi)

theorem normW_eq {t : Nat} (ht : P t) : g2NormW (unpack 4060 12 t) = normWK t := by
  unfold g2NormW normWK
  apply allLt_eq
  intro k hk
  obtain ⟨w1, w2⟩ := wg_eq hk
  obtain ⟨c1, c2⟩ := conj_eq ht w2
  rw [w1, c1, inW_eq c2]

theorem normV_eq {t : Nat} (ht : P t) : g2NormV (unpack 4060 12 t) = normVK t := by
  unfold g2NormV normVK
  apply allLt_eq
  intro k hk
  obtain ⟨v1, v2⟩ := vg_eq hk
  obtain ⟨c1, c2⟩ := conj_eq ht v2
  rw [v1, c1, inV_eq c2]

theorem centW_eq {t : Nat} (ht : P t) : g2CentW (unpack 4060 12 t) = centWK t := by
  unfold g2CentW centWK
  apply allLt_eq
  intro k hk
  obtain ⟨w1, w2⟩ := wg_eq hk
  obtain ⟨c1, c2⟩ := conj_eq ht w2
  rw [w1, ruConjA, c1, eq_eq c2 w2]

theorem centV_eq {t : Nat} (ht : P t) : g2CentV (unpack 4060 12 t) = centVK t := by
  unfold g2CentV centVK
  apply allLt_eq
  intro k hk
  obtain ⟨v1, v2⟩ := vg_eq hk
  obtain ⟨c1, c2⟩ := conj_eq ht v2
  rw [v1, ruConjA, c1, eq_eq c2 v2]

theorem sameW_eq {t u : Nat} (ht : P t) (hu : P u) :
    g2SameW (unpack 4060 12 t) (unpack 4060 12 u) = sameWK t u := by
  unfold g2SameW sameWK
  apply allLt_eq
  intro k hk
  obtain ⟨w1, w2⟩ := wg_eq hk
  obtain ⟨c1, c2⟩ := conj_eq ht w2
  obtain ⟨d1, d2⟩ := conj_eq hu w2
  rw [w1, ruConjA, ruConjA, c1, d1, eq_eq c2 d2]

theorem na_eq {j : Nat} (hj : j < 2) : g2NA j = unpack 4060 12 (NAk j) ∧ P (NAk j) := by
  interval_cases j <;> exact cw_eq (by decide)

theorem xa_eq : g2XA = unpack 4060 12 XAk ∧ P XAk := cw_eq (by decide)

theorem aa_eq {i : Nat} (hi : i < 3) : g2AA i = unpack 4060 12 (AAk i) ∧ P (AAk i) := by
  interval_cases i <;> exact cw_eq (by decide)

theorem comm_eq {t u : Nat} (ht : P t) (hu : P u) :
    g2CommA (unpack 4060 12 t) (unpack 4060 12 u) = unpack 4060 12 (commK t u) ∧ P (commK t u) := by
  obtain ⟨c1, c2⟩ := conj_eq ht hu
  unfold g2CommA
  rw [ruConjA, c1, inv_eq hu, comp_eq c2 (P_pinv hu)]
  exact ⟨rfl, P_pc c2 (P_pinv hu)⟩

theorem da_eq {m : Nat} (hm : m < 3) : g2DA m = unpack 4060 12 (DAk m) ∧ P (DAk m) := by
  have key : ∀ j k, j < 2 → k < 3 → (g2DIdx.getD m (0, 0)) = (j, k) →
      g2DA m = unpack 4060 12 (DAk m) ∧ P (DAk m) := by
    intro j k hj hk he
    obtain ⟨v1, v2⟩ := vg_eq hk
    obtain ⟨n1, n2⟩ := na_eq hj
    obtain ⟨c1, c2⟩ := conj_eq (P_pinv n2) v2
    unfold g2DA DAk
    rw [he, v1, n1, inv_eq n2, ruConjA, c1, comp_eq v2 c2]
    exact ⟨rfl, P_pc v2 c2⟩
  interval_cases m
  · exact key 0 1 (by norm_num) (by norm_num) rfl
  · exact key 0 2 (by norm_num) (by norm_num) rfl
  · exact key 1 1 (by norm_num) (by norm_num) rfl

theorem dprod_eq (e : Nat) : g2DProd e = unpack 4060 12 (DPk e) ∧ P (DPk e) := by
  obtain ⟨d0, p0⟩ := da_eq (m := 0) (by norm_num)
  obtain ⟨d1, p1⟩ := da_eq (m := 1) (by norm_num)
  obtain ⟨d2, p2⟩ := da_eq (m := 2) (by norm_num)
  unfold g2DProd
  rw [d0, d1, d2]
  exact prod3 p0 p1 p2 e

theorem aprod_eq (e : Nat) : g2AProd e = unpack 4060 12 (APk e) ∧ P (APk e) := by
  obtain ⟨a0, p0⟩ := aa_eq (i := 0) (by norm_num)
  obtain ⟨a1, p1⟩ := aa_eq (i := 1) (by norm_num)
  obtain ⟨a2, p2⟩ := aa_eq (i := 2) (by norm_num)
  unfold g2AProd
  rw [a0, a1, a2]
  exact prod3 p0 p1 p2 e

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Quasithin.H13.Ch4.G2Ru in
open Certificates in
theorem c7164 :
    g2CentV g2XA = true ∧ g2NormW g2XA = false ∧
      (∀ j < 2, g2NormW (g2NA j) = true ∧ g2NormV (g2NA j) = true ∧
        g2NormW (g2CommA (g2NA j) g2XA) = true) ∧
      (∀ m < 3, g2InV (g2DA m) = true) ∧
      (∀ i < 8, ∀ j < 8, i < j → eqA 4060 (g2DProd i) (g2DProd j) = false) ∧
      (∀ i < 3, g2NormW (g2AA i) = true ∧ g2CentV (g2AA i) = true ∧
        g2CentW (compA 4060 (g2AA i) (g2AA i)) = true) ∧
      (∀ i < 3, ∀ j < 3,
        g2SameW (compA 4060 (g2AA i) (g2AA j)) (compA 4060 (g2AA j) (g2AA i)) = true) ∧
      (∀ e < 8, ∀ e' < 8, e < e' → g2SameW (g2AProd e) (g2AProd e') = false) := by
  obtain ⟨xa1, xa2⟩ := xa_eq
  have h3 := k3
  have h4 := k4
  have h5 := k5
  have h6 := k6
  have h7 := k7
  have h8 := k8
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at h3 h4 h5 h6 h7 h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [xa1, centV_eq xa2]
    exact k1
  · rw [xa1, normW_eq xa2]
    simpa using k2
  · intro j hj
    obtain ⟨n1, n2⟩ := na_eq hj
    obtain ⟨⟨r1, r2⟩, r3⟩ := h3 j hj
    obtain ⟨c1, c2⟩ := comm_eq n2 xa2
    rw [n1, xa1, normW_eq n2, normV_eq n2, c1, normW_eq c2]
    exact ⟨r1, r2, r3⟩
  · intro m hm
    obtain ⟨d1, d2⟩ := da_eq hm
    rw [d1, inV_eq d2]
    exact h4 m hm
  · intro i hi j hj hij
    rw [(dprod_eq i).1, (dprod_eq j).1, eq_eq (dprod_eq i).2 (dprod_eq j).2]
    rcases h5 i hi j hj with h | h
    · omega
    · exact h
  · intro i hi
    obtain ⟨a1, a2⟩ := aa_eq hi
    obtain ⟨⟨r1, r2⟩, r3⟩ := h6 i hi
    rw [a1, normW_eq a2, centV_eq a2, comp_eq a2 a2, centW_eq (P_pc a2 a2)]
    exact ⟨r1, r2, r3⟩
  · intro i hi j hj
    obtain ⟨a1, a2⟩ := aa_eq hi
    obtain ⟨b1, b2⟩ := aa_eq hj
    rw [a1, b1, comp_eq a2 b2, comp_eq b2 a2, sameW_eq (P_pc a2 b2) (P_pc b2 a2)]
    exact h7 i hi j hj
  · intro e he e' he' hee
    rw [(aprod_eq e).1, (aprod_eq e').1, sameW_eq (aprod_eq e).2 (aprod_eq e').2]
    rcases h8 e he e' he' with h | h
    · omega
    · exact h

end CertificateChecks.KernelSporSch.G2Ru7164

end
