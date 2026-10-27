module

public import Certificates.Data.OmegaSevenMax.Defs
public import Certificates.Data.OmegaSevenMax.RootCodes
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Card
public import Certificates.Kernel.E7Orbit.Nodes
public import Certificates.Kernel.E7Orbit.Gens
public import CFSG.Certificates.Kernel.E7Orbit.Forest
public import CFSG.Certificates.Kernel.E7Orbit.Vec
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetFacts
import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.PackSetSound
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
public import Certificates.Certificate709545Base
public import Mathlib.GroupTheory.Perm.Basic
import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE7Orbit

open Equiv Certificates.OmegaSevenMax CFSG.KC.E7Orbit CFSG.KC.Benes CFSG.KC.Enum
open CFSG.OddStandard.SmallF3.Omega.E7RootSet (encV_decV)
open CFSG.KC.Pack (allN_spec)
open scoped Pointwise

#kc_forall_tree chunks_ok
  (fun c => CFSG.KC.E7Orbit.chunkOK CertificateChecks.KernelE7Orbit.T
    CertificateChecks.KernelE7Orbit.NT CertificateChecks.KernelE7Orbit.MS c = true) 50
  CertificateChecks.KernelE7Orbit.ch709545n

theorem nodes_ok : ∀ i < 3159, nodeOK T NT MS i = true := nodes_of_chunks chunks_ok

theorem ms0 : MS 0 = 3151 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ms1 : MS 1 = 1567 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ms2 : MS 2 = 1035 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ms3 : MS 3 = 1626 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ms4 : MS 4 = 1 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ms5 : MS 5 = 11 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ms6 : MS 6 = 2 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem blk0 : blkF (recAt T 3151) = 0 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem ms_lt (d : Fin 4) : MS d < 3159 := by
  fin_cases d
  · exact lt_of_eq_of_lt ms0 (by decide)
  · exact lt_of_eq_of_lt ms1 (by decide)
  · exact lt_of_eq_of_lt ms2 (by decide)
  · exact lt_of_eq_of_lt ms3 (by decide)

theorem decV_inj {c d : Nat} (hc : c < 2187) (hd : d < 2187) (h : decV c = decV d) : c = d := by
  rw [← encV_decV hc, ← encV_decV hd, h]

theorem polarV_self (u : V) : polarV u u = 2 * qV u := by
  unfold polarV qV
  ring

theorem rxV_rxV {u : V} (hu : qV u = 1) (x : V) : rxV u (rxV u x) = x := by
  have hl : polarV u (x - polarV u x • u) = polarV u x - polarV u x * polarV u u := by
    unfold polarV
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  funext i
  simp only [rxV, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hl, polarV_self, hu]
  ring

theorem rxN_rxN {u : Nat} (hu : qV (decV u) = 1) {c : Nat} (hc : c < 2187) :
    rxN u (rxN u c) = c :=
  decV_inj (rxN_lt _ _) hc (by rw [decV_rxN, decV_rxN, rxV_rxV hu])

@[expose] noncomputable def rF (u : Nat) (c : Fin 2187) : Fin 2187 := ⟨rxN u c.val, rxN_lt u c.val⟩

theorem rF_val (u : Nat) (c : Fin 2187) : (rF u c).val = rxN u c.val := by
  unfold rF
  exact Fin.val_mk _

theorem rF_rF {u : Nat} (hu : qV (decV u) = 1) (c : Fin 2187) : rF u (rF u c) = c := by
  apply Fin.ext
  rw [rF_val, rF_val]
  exact rxN_rxN hu c.2

@[expose] noncomputable def rP (u : Nat) (hu : qV (decV u) = 1) : Perm (Fin 2187) :=
  ⟨rF u, rF u, rF_rF hu, rF_rF hu⟩

theorem rP_val (u : Nat) (hu : qV (decV u) = 1) (c : Fin 2187) : (rP u hu c : Nat) = rxN u c :=
  rF_val u c

theorem q1 : qV (decV 1) = 1 := by decide

theorem qe : ∀ j < 6, qV (decV (3 ^ (j + 1))) = 1 := by decide

@[expose] noncomputable def σ (j : Nat) : Perm (Fin 2187) :=
  if h : j < 6 then rP 1 q1 * rP (3 ^ (j + 1)) (qe j h) else 1

theorem σ_val {j : Nat} (hj : j < 6) (c : Fin 2187) : (σ j c : Nat) = hN j c := by
  unfold σ
  rw [dif_pos hj, Perm.mul_apply, rP_val, rP_val]
  rfl

theorem decV_σ (j : Fin 6) (c : Fin 2187) : decV (σ j c) = hV j (decV c) := by
  rw [σ_val j.2, decV_hN]
  rfl

theorem bindH : ∀ l < 6, bindOK NT (hP l) l = true := by
  intro l hl
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact bindH0
  · exact bindH1
  · exact bindH2
  · exact bindH3
  · exact bindH4
  · exact bindH5

theorem hnet : ∀ l < 6, StagesValid 12 (NT l) ∧
    ∀ p : Fin 2187, benesPerm 12 (NT l) p = ((σ l)⁻¹ p : Nat) := by
  intro l hl
  refine netActs_of_bind (bindH l hl) fun q => ?_
  rw [σ_val hl]
  exact pg_packF (fun c _ => lt_trans (rxN_lt _ _) (by decide)) q.2

@[expose] noncomputable def wPerm (w : List (Fin 6)) : Perm (Fin 2187) :=
  (w.map fun j : Fin 6 => σ j.val).prod

theorem forest_words : ∀ i < 3159, ∃ w : List (Fin 6), maskSet (msk (recAt T i)) =
    wPerm w • maskSet (msk (recAt T (MS (blkF (recAt T i))))) := by
  suffices key : ∀ d, ∀ i < 3159, depF (recAt T i) = d → ∃ w : List (Fin 6),
      maskSet (msk (recAt T i)) = wPerm w • maskSet (msk (recAt T (MS (blkF (recAt T i))))) from
    fun i hi => key _ i hi rfl
  intro d
  induction d with
  | zero =>
    intro i hi hd
    have e := (nodeOK_sound (nodes_ok i hi)).2.2.2.1 hd
    refine ⟨[], ?_⟩
    rw [wPerm, List.map_nil, List.prod_nil, one_smul, ← e]
  | succ d ih =>
    intro i hi hd
    obtain ⟨hp, hl, hdp, hbp, himg⟩ := (nodeOK_sound (nodes_ok i hi)).2.2.2.2 (by omega)
    obtain ⟨w, e⟩ := ih _ hp (by omega)
    obtain ⟨hv, hb⟩ := hnet _ hl
    have hs := (img_sound hv hb (msk_lt nodes_ok hp)).1
    rw [himg] at hs
    refine ⟨⟨letF (recAt T i), hl⟩ :: w, ?_⟩
    rw [hs, e, hbp, wPerm, wPerm, List.map_cons, List.prod_cons, mul_smul]

open Classical in
@[expose] noncomputable def toV (A : Set (Fin 2187)) : Finset V :=
  ((Finset.univ : Finset (Fin 2187)).filter (· ∈ A)).image fun c : Fin 2187 => decV c.val

theorem mem_toV {A : Set (Fin 2187)} {x : V} : x ∈ toV A ↔ ∃ c ∈ A, decV c = x := by
  unfold toV
  simp

theorem toV_inj {A B : Set (Fin 2187)} (h : toV A = toV B) : A = B := by
  have key : ∀ {A B : Set (Fin 2187)}, toV A = toV B → ∀ c ∈ A, c ∈ B := by
    intro A B h c hc
    have hx : decV c ∈ toV B := h ▸ mem_toV.2 ⟨c, hc, rfl⟩
    obtain ⟨d, hd, e⟩ := mem_toV.1 hx
    rwa [Fin.ext (decV_inj d.2 c.2 e)] at hd
  ext c
  exact ⟨key h c, key h.symm c⟩

theorem toV_smul {g : Perm (Fin 2187)} {F : V → V} (hg : ∀ c, decV (g c) = F (decV c))
    (A : Set (Fin 2187)) : toV (g • A) = (toV A).image F := by
  ext x
  rw [mem_toV, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hc
    exact ⟨decV y, mem_toV.2 ⟨y, hy, rfl⟩, (hg y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := mem_toV.1 hy
    exact ⟨g c, Set.smul_mem_smul_set hc, hg c⟩

theorem decV_wPerm (w : List (Fin 6)) (c : Fin 2187) : decV (wPerm w c) = hWord w (decV c) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    rw [wPerm, List.map_cons, List.prod_cons, Perm.mul_apply, decV_σ]
    change hV j (decV ((w.map fun j : Fin 6 => σ j.val).prod c)) = hV j (hWord w (decV c))
    rw [← ih]
    rfl

@[expose] noncomputable def nodeV (n : Nat) : Finset V := toV (maskSet (msk (recAt T n)))

theorem nodeV_inj {n m : Nat} (hn : n < 3159) (hm : m < 3159) (h : nodeV n = nodeV m) : n = m :=
  nodes_inj nodes_ok hn hm (toV_inj h)

theorem rootCodes_lt : ∀ p ∈ rootCodes, p < 2187 := by decide

theorem toV_wordMask {w : Nat} {F : V → V} (hF : ∀ p, decV (wordPt 32 w p) = F (decV p))
    (hlt : ∀ p ∈ rootCodes, wordPt 32 w p < 2187) :
    toV (maskSet (wordMask w rootCodes)) = rootSetV.image F := by
  ext x
  rw [mem_toV, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨p, hp, e⟩ := testBit_wordMask.1 hc
    refine ⟨decV p, ?_, ?_⟩
    · rw [rootSetV, List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, rfl⟩
    · rw [← hF, e]
  · rintro ⟨y, hy, rfl⟩
    rw [rootSetV, List.mem_toFinset, List.mem_map] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    refine ⟨⟨wordPt 32 w p, hlt p hp⟩, testBit_wordMask.2 ⟨p, hp, rfl⟩, hF p⟩

theorem uP0 : pg 12 4095 uP 0 = 194 := rfl
theorem uP1 : pg 12 4095 uP 1 = 307 := rfl
theorem uP2 : pg 12 4095 uP 2 = 585 := rfl
theorem wP0 : pg 12 4095 wP 0 = 324 := rfl
theorem wP1 : pg 12 4095 wP 1 = 1216 := rfl
theorem wP2 : pg 12 4095 wP 2 = 2135 := rfl

theorem qg : qV (decV 194) = 1 ∧ qV (decV 307) = 1 ∧ qV (decV 585) = 1 ∧ qV (decV 324) = 1 ∧
    qV (decV 1216) = 1 ∧ qV (decV 2135) = 1 := by decide

theorem wordPt1 (p : Nat) : wordPt 32 1 p = gF 0 p := by
  rw [wordPt_succ 31 1 p (by decide)]
  exact wordPt_zero 31 _

theorem wordPt2 (p : Nat) : wordPt 32 2 p = gF 1 p := by
  rw [wordPt_succ 31 2 p (by decide)]
  exact wordPt_zero 31 _

theorem wordPt11 (p : Nat) : wordPt 32 11 p = gF 0 (gF 2 p) := by
  rw [wordPt_succ 31 11 p (by decide)]
  rw [wordPt_succ 30 1 _ (by decide)]
  exact wordPt_zero 30 _

theorem gF_lt (k p : Nat) : gF k p < 2187 := rxN_lt _ _

theorem pairWord_append (L L' : List (V × V)) :
    pairWord (L ++ L') = pairWord L ∘ pairWord L' := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    change rxV x.1 ∘ rxV x.2 ∘ pairWord (L ++ L') = (rxV x.1 ∘ rxV x.2 ∘ pairWord L) ∘ pairWord L'
    rw [ih]
    rfl

@[expose] noncomputable def hPair (j : Fin 6) : V × V := (decV 1, decV (3 ^ (j.val + 1)))

theorem hWord_eq (w : List (Fin 6)) : hWord w = pairWord (w.map hPair) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change hV j ∘ hWord w = rxV (hPair j).1 ∘ rxV (hPair j).2 ∘ pairWord (w.map hPair)
    rw [ih]
    rfl

theorem rootV (d : Fin 4) : ∃ L : List (V × V), (∀ x ∈ L, qV x.1 = 1 ∧ qV x.2 = 1) ∧
    nodeV (MS d) = rootSetV.image (pairWord L) := by
  have hroots := allN_spec roots
  fin_cases d
  · refine ⟨[], fun x hx => absurd hx List.not_mem_nil, ?_⟩
    have e := Nat.eq_of_beq_eq_true u0
    change toV (maskSet (rootM 0)) = _
    rw [e, toV_wordMask (F := id) (fun p => by rw [wordPt_zero]; rfl)
      (fun p hp => by rw [wordPt_zero]; exact rootCodes_lt p hp)]
    rfl
  · refine ⟨[(decV 194, decV 324)], fun x hx => ?_, ?_⟩
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨qg.1, qg.2.2.2.1⟩
    · have e := Nat.eq_of_beq_eq_true (hroots 0 (by decide))
      change toV (maskSet (rootM 1)) = _
      rw [e, ms4, toV_wordMask (F := pairWord [(decV 194, decV 324)])
        (fun p => by rw [wordPt1, decV_gF, uP0, wP0]; rfl)
        (fun p _ => by rw [wordPt1]; exact gF_lt _ _)]
  · refine ⟨[(decV 194, decV 324), (decV 585, decV 2135)], fun x hx => ?_, ?_⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact ⟨qg.1, qg.2.2.2.1⟩
      · exact ⟨qg.2.2.1, qg.2.2.2.2.2⟩
    · have e := Nat.eq_of_beq_eq_true (hroots 1 (by decide))
      change toV (maskSet (rootM 2)) = _
      rw [e, ms5, toV_wordMask (F := pairWord [(decV 194, decV 324), (decV 585, decV 2135)])
        (fun p => by rw [wordPt11, decV_gF, decV_gF, uP0, wP0, uP2, wP2]; rfl)
        (fun p _ => by rw [wordPt11]; exact gF_lt _ _)]
  · refine ⟨[(decV 307, decV 1216)], fun x hx => ?_, ?_⟩
    · rw [List.mem_singleton] at hx
      subst hx
      exact ⟨qg.2.1, qg.2.2.2.2.1⟩
    · have e := Nat.eq_of_beq_eq_true (hroots 2 (by decide))
      change toV (maskSet (rootM 3)) = _
      rw [e, ms6, toV_wordMask (F := pairWord [(decV 307, decV 1216)])
        (fun p => by rw [wordPt2, decV_gF, uP1, wP1]; rfl)
        (fun p _ => by rw [wordPt2]; exact gF_lt _ _)]

theorem nodeV_root : nodeV 3151 = rootSetV := by
  obtain ⟨L, -, e⟩ := rootV 0
  rw [← ms0]
  have e0 := Nat.eq_of_beq_eq_true u0
  change toV (maskSet (rootM 0)) = _
  rw [e0, toV_wordMask (F := id) (fun p => by rw [wordPt_zero]; rfl)
    (fun p hp => by rw [wordPt_zero]; exact rootCodes_lt p hp)]
  exact Finset.image_id

theorem hV_fix (j : Fin 6) : rootSetV.image (hV j) = rootSetV := by
  have e := Nat.eq_of_beq_eq_true (allN_spec hfix j j.2)
  have hlt : rootM 0 < 2 ^ 2187 := msk_lt nodes_ok (ms_lt 0)
  obtain ⟨hv, hb⟩ := hnet j j.2
  have hs := (img_sound hv hb hlt).1
  rw [e] at hs
  have h2 := congrArg toV hs
  rw [toV_smul (decV_σ j)] at h2
  have h0 : toV (maskSet (rootM 0)) = rootSetV := by
    have := nodeV_root
    rw [← ms0] at this
    exact this
  rw [h0] at h2
  exact h2.symm

@[expose] noncomputable def π : Perm (Fin 3159) := swap 0 ⟨3151, by decide⟩

@[expose] noncomputable def pS (i : Fin 3159) : Finset V := nodeV (π i)

theorem blk_lt (n : Fin 3159) : blkF (recAt T n) < 4 := (nodeOK_sound (nodes_ok n n.2)).2.2.1

@[expose] noncomputable def cS (i : Fin 3159) : Fin 4 := ⟨blkF (recAt T (π i)), blk_lt _⟩

@[expose] noncomputable def rS (d : Fin 4) : Fin 3159 := π ⟨MS d, ms_lt d⟩

theorem card_cls (d : Fin 4) : (Finset.univ.filter (cS · = d)).card =
    ((Finset.range 3159).filter fun n => blkF (recAt T n) = d).card := by
  refine Finset.card_bij (fun i _ => (π i).val) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_range.2 (π i).2, congrArg Fin.val hi.2⟩
  · intro i _ j _ h
    exact π.injective (Fin.ext h)
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    refine ⟨π ⟨n, hn.1⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, Fin.ext ?_⟩
      change blkF (recAt T (π (π ⟨n, hn.1⟩))) = d
      rw [π, swap_apply_self]
      exact hn.2
    · change (π (π ⟨n, hn.1⟩)).val = n
      rw [π, swap_apply_self]

theorem cS_zero (i : Fin 3159) : cS i = 0 ↔ i = 0 := by
  constructor
  · intro h
    have hc := cntOK_sound cnt (fun n hn => blk_lt ⟨n, hn⟩) 0 (by decide)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
    have h1 : (π i).val ∈ (Finset.range 3159).filter fun n => blkF (recAt T n) = 0 := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨(π i).2, congrArg Fin.val h⟩
    have h2 : 3151 ∈ (Finset.range 3159).filter fun n => blkF (recAt T n) = 0 := by
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by decide, blk0⟩
    rw [ha, Finset.mem_singleton] at h1 h2
    have e : π i = ⟨3151, by decide⟩ := Fin.ext (h1.trans h2.symm)
    have e2 := congrArg π e
    rw [π, swap_apply_self, swap_apply_right] at e2
    exact e2
  · rintro rfl
    refine Fin.ext ?_
    change blkF (recAt T (π 0)) = 0
    rw [π, swap_apply_left]
    exact blk0

theorem orbit_facts : ∃ (p : Fin 3159 → Finset V) (c : Fin 3159 → Fin 4) (r : Fin 4 → Fin 3159),
    Function.Injective p ∧ p 0 = rootSetV ∧
    (∀ i, ∃ L : List (V × V), (∀ x ∈ L, qV x.1 = 1 ∧ qV x.2 = 1) ∧
      p i = rootSetV.image (pairWord L)) ∧
    (∀ i, ∃ w : List (Fin 6), p i = (p (r (c i))).image (hWord w)) ∧
    (∀ i, c i = 0 ↔ i = 0) ∧
    (∀ d, (Finset.univ.filter (c · = d)).card = ![1, 288, 630, 2240] d) ∧
    ∀ j, rootSetV.image (hV j) = rootSetV := by
  have hstep : ∀ i, ∃ w : List (Fin 6), pS i = (pS (rS (cS i))).image (hWord w) := by
    intro i
    obtain ⟨w, e⟩ := forest_words _ (π i).2
    refine ⟨w, ?_⟩
    have e2 : pS (rS (cS i)) = nodeV (MS (blkF (recAt T (π i)))) := by
      change nodeV (π (π _)) = _
      rw [π, swap_apply_self]
      rfl
    rw [e2]
    change toV (maskSet (msk (recAt T (π i)))) = _
    rw [e, toV_smul (decV_wPerm w)]
    rfl
  refine ⟨pS, cS, rS, ?_, ?_, ?_, hstep, cS_zero, ?_, hV_fix⟩
  · intro i k h
    exact π.injective (Fin.ext (nodeV_inj (π i).2 (π k).2 h))
  · change nodeV (π 0) = _
    rw [π, swap_apply_left]
    exact nodeV_root
  · intro i
    obtain ⟨w, e⟩ := hstep i
    obtain ⟨L, hL, eL⟩ := rootV (cS i)
    have e2 : pS (rS (cS i)) = nodeV (MS (cS i)) := by
      change nodeV (π (π _)) = _
      rw [π, swap_apply_self]
    refine ⟨w.map hPair ++ L, fun x hx => ?_, ?_⟩
    · rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
        exact ⟨q1, qe j j.2⟩
      · exact hL x hx
    · rw [e, e2, eL, Finset.image_image, pairWord_append, hWord_eq]
  · intro d
    rw [card_cls, cntOK_sound cnt (fun n hn => blk_lt ⟨n, hn⟩) d d.2]
    fin_cases d <;> rfl

end CertificateChecks.KernelE7Orbit

end
