module

public import Certificates.Kernel.RouteP.Pres.Rep
public import Certificates.Kernel.RouteP.Bridge.Ws
public import Certificates.Kernel.RouteP.Bridge.Fix
public import Certificates.Kernel.RouteP.Bridge.Rel0
public import Certificates.Kernel.RouteP.Bridge.Rel1
public import Certificates.Kernel.RouteP.Bridge.Rel2
public import Certificates.Kernel.RouteP.Bridge.Rel3
public import CFSG.Certificates.Kernel.RouteP.LocalBFS
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Tables
import CFSG.Certificates.Kernel.Common.ForallTreeFrom

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

#kc_forall_tree qck0_all (fun g => CFSG.KD.RouteP.qck0 g = true) 640 CFSG.KD.RouteP.BridgeCk.q
#kc_forall_tree qck1_all (fun g => CFSG.KD.RouteP.qck1 g = true) 560 CFSG.KD.RouteP.BridgeCk.s
#kc_forall_tree qck2_all (fun g => CFSG.KD.RouteP.qck2 g = true) 100 CFSG.KD.RouteP.BridgeCk.t
#kc_forall_tree qckU3_all (fun g => CFSG.KD.RouteP.qckU3 g = true) 320 CFSG.KD.RouteP.BridgeCk.r
#kc_forall_tree uckU3_all (fun k => CFSG.KD.RouteP.uckU3 k = true) 21 CFSG.KD.RouteP.BridgeCk.u

theorem uckU3_lt : ∀ k < 21, uckU3 k = true := uckU3_all
#kc_forall_tree fixck_all (fun j => CFSG.KD.RouteP.fixck j = true) 10 CFSG.KD.RouteP.BridgeCk.f

theorem gq_act {i : Nat} (hi : i < 22) (y : Pt) :
    (gq i y).val = eL NWP KAP KBP (cq ((i + 1 : Nat) : ℤ)) y.val ∧
      ((gq i)⁻¹ y).val = eL NWP KAP KBP (cq (-((i + 1 : Nat) : ℤ))) y.val := by
  by_cases h11 : i < 11
  · have eg : gq i = gP (28 + i) := ite_eq_left h11
    have e1 : cq ((i + 1 : Nat) : ℤ) = Int.negSucc (28 + i) := by
      unfold cq
      rw [ite_eq_left (by omega), ite_eq_left (by omega), Int.negSucc_eq]
      omega
    have e2 : cq (-((i + 1 : Nat) : ℤ)) = Int.ofNat (28 + i + 1) := by
      unfold cq
      rw [ite_eq_left (by omega), ite_eq_right (by omega), Int.ofNat_eq_natCast]
      omega
    rw [eg, e1, e2]
    exact ⟨gT_apply (lokP (by simp; omega)) y, gT_inv_apply (lokP (by simp; omega)) y⟩
  · by_cases h21 : i = 21
    · subst h21
      have eg : gq 21 = gP 41 := rfl
      have e1 : cq ((21 + 1 : Nat) : ℤ) = Int.negSucc 41 := rfl
      have e2 : cq (-((21 + 1 : Nat) : ℤ)) = Int.ofNat (41 + 1) := rfl
      rw [eg, e1, e2]
      exact ⟨gT_apply (lokP (by decide)) y, gT_inv_apply (lokP (by decide)) y⟩
    · have eg : gq i = 1 := by
        unfold gq
        rw [ite_eq_right h11, ite_eq_right h21]
      have e1 : cq ((i + 1 : Nat) : ℤ) = Int.ofNat 0 := by
        unfold cq
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rfl
      have e2 : cq (-((i + 1 : Nat) : ℤ)) = Int.ofNat 0 := by
        unfold cq
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        rfl
      rw [eg, e1, e2, inv_one]
      exact ⟨(eL_zero NWP KAP KBP y.isLt).symm, (eL_zero NWP KAP KBP y.isLt).symm⟩

theorem letterPerm_act {l : ℤ} (hl : 1 ≤ l.natAbs ∧ l.natAbs ≤ 22) (y : Pt) :
    (letterPerm gq 22 l y).val = eL NWP KAP KBP (cq l) y.val := by
  unfold letterPerm
  by_cases hp : 0 < l
  · rw [ite_eq_left ⟨hp, by omega⟩]
    have e : l = (((l - 1).toNat + 1 : Nat) : ℤ) := by omega
    conv_rhs => rw [e]
    exact (gq_act (by omega) y).1
  · rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩]
    have e : l = -(((-l - 1).toNat + 1 : Nat) : ℤ) := by omega
    conv_rhs => rw [e]
    exact (gq_act (by omega) y).2

theorem relsQ_length : relsQ.length = 256 := by decide +kernel

theorem relsQ_letters : ∀ w ∈ relsQ, ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 22 := by decide +kernel

theorem NWU3_of_ne {j : Nat} (h : j ≠ 42) : NWU3 j = NWP j := by
  funext l
  have e : Nat.beq j 42 = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
  unfold NWU3
  rw [e]

theorem kapOK_U3 {j : Nat} (h : j ≠ 42) : kapOK KAU3 KBU3 j = kapOK KAP KBP j := by
  unfold kapOK KAU3 KBU3 KAP KBP
  rw [NWU3_of_ne h]

theorem eL_congr {NW NW' : Nat → Nat → Nat} {KA KB KA' KB' : Nat → Nat} {z : ℤ}
    (h1 : NW (z.natAbs - 1) = NW' (z.natAbs - 1)) (h2 : KA (z.natAbs - 1) = KA' (z.natAbs - 1))
    (h3 : KB (z.natAbs - 1) = KB' (z.natAbs - 1)) : eL NW KA KB z = eL NW' KA' KB' z := by
  funext N
  cases z with
  | ofNat m =>
    change NW (m - 1) = NW' (m - 1) at h1
    change KA (m - 1) = KA' (m - 1) at h2
    change KB (m - 1) = KB' (m - 1) at h3
    simp only [eL, fibF, lK, h1, h2, h3]
  | negSucc n =>
    change NW n = NW' n at h1
    change KA n = KA' n at h2
    change KB n = KB' n at h3
    simp only [eL, fibF, lK, h1, h2, h3]

theorem eW_U3 : ∀ w : List ℤ, (∀ z ∈ w, z.natAbs - 1 ≠ 42) → eW NWU3 KAU3 KBU3 w = eW NWP KAP KBP w
  | [], _ => rfl
  | z :: w, h => by
    funext N
    have hz := h z List.mem_cons_self
    have h2 : KAU3 (z.natAbs - 1) = KAP (z.natAbs - 1) := by
      unfold KAU3 KAP
      rw [NWU3_of_ne hz]
    have h3 : KBU3 (z.natAbs - 1) = KBP (z.natAbs - 1) := by
      unfold KBU3 KBP
      rw [NWU3_of_ne hz]
    rw [eW_cons, eW_cons, eW_U3 w (fun z' hz' => h z' (List.mem_cons_of_mem z hz')),
      eL_congr (NWU3_of_ne hz) h2 h3]

theorem eW_append (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) :
    ∀ (a b : List ℤ) (N : Nat), eW NW KA KB (a ++ b) N = eW NW KA KB a (eW NW KA KB b N)
  | [], _, _ => rfl
  | z :: a, b, N => by rw [List.cons_append, eW_cons, eW_cons, eW_append NW KA KB a b N]

theorem eW_replicate {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} {z : ℤ} {w t : List ℤ}
    (hz : ∀ N < 920808, eL NW KA KB z N = eW NW KA KB w N) (hw : ∀ y ∈ w, LOK NW KA KB y)
    (ht : ∀ y ∈ t, LOK NW KA KB y) :
    ∀ (k : Nat) {N : Nat}, N < 920808 →
      eW NW KA KB (List.replicate k z ++ t) N = eW NW KA KB ((List.replicate k w).flatten ++ t) N
  | 0, _, _ => rfl
  | k + 1, N, hN => by
    have hl : ∀ y ∈ (List.replicate k w).flatten ++ t, LOK NW KA KB y := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨l, hl, hy⟩ := List.mem_flatten.1 hy
        rw [(List.mem_replicate.1 hl).2] at hy
        exact hw y hy
      · exact ht y hy
    rw [List.replicate_succ, List.cons_append, eW_cons, eW_replicate hz hw ht k hN,
      hz _ (eW_lt _ hl hN), List.replicate_succ, List.flatten_cons, List.append_assoc, eW_append NW KA KB w]

theorem lokU3 {z : ℤ} (hz : z.natAbs - 1 < 43) : LOK NWU3 KAU3 KBU3 z := by
  by_cases h : z.natAbs - 1 = 42
  · have e : uckU3 20 = andB (CFSG.KC.Fi24Net.netOK (NWU3 42)) (kapOK KAU3 KBU3 42) := rfl
    have h20 := uckU3_lt 20 (by decide)
    rw [e] at h20
    unfold LOK
    rw [h]
    exact CFSG.KC.Benes.andB_true h20
  · have hp := lokP (z := z) (by omega)
    unfold LOK at hp ⊢
    rw [NWU3_of_ne h, kapOK_U3 h]
    exact hp

theorem wU3_letters : ∀ z ∈ wU3, z.natAbs - 1 < 42 := by decide

theorem eL_U3 : ∀ N < 920808, eL NWU3 KAU3 KBU3 (43 : ℤ) N = eW NWU3 KAU3 KBU3 wU3 N := by
  have hl := lokU3 (z := 43) (by decide)
  have hw : WOK NWU3 KAU3 KBU3 wU3 := fun z hz => lokU3 (by have := wU3_letters z hz; omega)
  have e19 : uckU3 19 = wordKOK NWU3 KAU3 KBU3 wU3 42 := rfl
  have h19 := uckU3_lt 19 (by decide)
  rw [e19] at h19
  exact word_spec hl.1 hl.2 hw (fun k hk => by
    have h := uckU3_lt k (by omega)
    unfold uckU3 at h
    rw [Nat.blt_eq.mpr hk] at h
    exact h) h19

theorem qw_letters {i : Nat} (hi : i < 256) : ∀ z ∈ qw i, z.natAbs - 1 < 42 := by
  intro z hz
  have hi0 : i < relsQ.length := by rw [relsQ_length]; exact hi
  unfold qw at hz
  rw [getElem!_pos relsQ i hi0] at hz
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
  have := relsQ_letters _ (List.getElem_mem hi0) l hl
  unfold cq
  split_ifs <;> omega

section Derive

variable {NW : Nat → Nat → Nat} {KA KB : Nat → Nat}

theorem LOK.neg {z : ℤ} (hz : LOK NW KA KB z) : LOK NW KA KB (-z) := by
  unfold LOK at hz ⊢
  rwa [Int.natAbs_neg]

theorem eL_neg_eL {z : ℤ} (hz : LOK NW KA KB z) {N : Nat} (hN : N < 920808) :
    eL NW KA KB (-z) (eL NW KA KB z N) = N := by
  obtain ⟨hn, hk⟩ := hz
  cases z with
  | ofNat m =>
    cases m with
    | zero =>
      change eL NW KA KB (Int.ofNat 0) (eL NW KA KB (Int.ofNat 0) N) = N
      rw [eL_zero _ _ _ hN, eL_zero _ _ _ hN]
    | succ n => exact (eL_pos_neg (n := n) hn hk hN).2.2.2
  | negSucc n => exact (eL_pos_neg (n := n) hn hk hN).2.1

theorem eL_eL_neg {z : ℤ} (hz : LOK NW KA KB z) {N : Nat} (hN : N < 920808) :
    eL NW KA KB z (eL NW KA KB (-z) N) = N := by
  have h := eL_neg_eL (LOK.neg hz) hN
  rwa [neg_neg] at h

theorem eW_inj : ∀ (a : List ℤ), (∀ z ∈ a, LOK NW KA KB z) → ∀ {X Y : Nat}, X < 920808 →
    Y < 920808 → eW NW KA KB a X = eW NW KA KB a Y → X = Y
  | [], _, _, _, _, _, h => h
  | z :: a, ha, X, Y, hX, hY, h => by
    rw [eW_cons, eW_cons] at h
    have hz := ha z List.mem_cons_self
    have ht : ∀ y ∈ a, LOK NW KA KB y := fun y hy => ha y (List.mem_cons_of_mem z hy)
    have h' := congrArg (eL NW KA KB (-z)) h
    rw [eL_neg_eL hz (eW_lt a ht hX), eL_neg_eL hz (eW_lt a ht hY)] at h'
    exact eW_inj a ht hX hY h'

theorem eW_swap {a b : List ℤ} (ha : ∀ z ∈ a, LOK NW KA KB z) (hb : ∀ z ∈ b, LOK NW KA KB z)
    (h : ∀ N < 920808, eW NW KA KB (a ++ b) N = N) : ∀ N < 920808, eW NW KA KB (b ++ a) N = N := by
  intro N hN
  have hM := eW_lt a ha hN
  have h2 := h _ hM
  rw [eW_append] at h2 ⊢
  exact eW_inj a ha (eW_lt b hb hM) hN h2

def wordRot (r : Nat) (u : List ℤ) : List ℤ := u.drop r ++ u.take r

def wordInv (u : List ℤ) : List ℤ := (u.map Neg.neg).reverse

theorem eW_wordRot {u : List ℤ} (hu : ∀ z ∈ u, LOK NW KA KB z) (h : ∀ N < 920808, eW NW KA KB u N = N)
    (r : Nat) : ∀ N < 920808, eW NW KA KB (wordRot r u) N = N :=
  eW_swap (fun z hz => hu z (List.mem_of_mem_take hz)) (fun z hz => hu z (List.mem_of_mem_drop hz))
    (by rw [List.take_append_drop]; exact h)

theorem wordInv_lok {u : List ℤ} (hu : ∀ z ∈ u, LOK NW KA KB z) : ∀ z ∈ wordInv u, LOK NW KA KB z := by
  intro z hz
  simp only [wordInv, List.mem_reverse, List.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact LOK.neg (hu y hy)

theorem eW_wordInv : ∀ (u : List ℤ), (∀ z ∈ u, LOK NW KA KB z) → ∀ N < 920808,
    eW NW KA KB (wordInv u) (eW NW KA KB u N) = N
  | [], _, _, _ => rfl
  | z :: u, hu, N, hN => by
    have ht : ∀ y ∈ u, LOK NW KA KB y := fun y hy => hu y (List.mem_cons_of_mem z hy)
    have e : wordInv (z :: u) = wordInv u ++ [-z] := by simp [wordInv]
    rw [e, eW_append, eW_cons]
    change eW NW KA KB (wordInv u) (eL NW KA KB (-z) (eL NW KA KB z (eW NW KA KB u N))) = N
    rw [eL_neg_eL (hu z List.mem_cons_self) (eW_lt u ht hN)]
    exact eW_wordInv u ht N hN

def freeStep (z : ℤ) (acc : List ℤ) : List ℤ :=
  if z = 0 then acc else
    match acc with
    | y :: r => if y = -z then r else z :: y :: r
    | [] => [z]

def wordRed (w : List ℤ) : List ℤ := w.foldr freeStep []

theorem freeStep_sub {z : ℤ} {acc : List ℤ} {y : ℤ} (hy : y ∈ freeStep z acc) : y = z ∨ y ∈ acc := by
  unfold freeStep at hy
  split_ifs at hy with h0
  · exact Or.inr hy
  · rcases acc with _ | ⟨x, r⟩
    · exact Or.inl (List.mem_singleton.1 hy)
    · simp only at hy
      split_ifs at hy with hx
      · exact Or.inr (List.mem_cons_of_mem _ hy)
      · exact List.mem_cons.1 hy

theorem wordRed_sub : ∀ (w : List ℤ), ∀ y ∈ wordRed w, y ∈ w
  | [], y, h => by simp [wordRed] at h
  | z :: w, y, h => by
    rcases freeStep_sub h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (wordRed_sub w y h)

theorem eW_freeStep {z : ℤ} {acc : List ℤ} (hz : LOK NW KA KB z) (hacc : ∀ y ∈ acc, LOK NW KA KB y)
    {N : Nat} (hN : N < 920808) : eW NW KA KB (freeStep z acc) N = eL NW KA KB z (eW NW KA KB acc N) := by
  unfold freeStep
  split_ifs with h0
  · subst h0
    exact (eL_zero _ _ _ (eW_lt acc hacc hN)).symm
  · rcases acc with _ | ⟨y, r⟩
    · rfl
    · simp only
      split_ifs with hy
      · subst hy
        rw [eW_cons, eL_eL_neg hz (eW_lt r (fun x hx => hacc x (List.mem_cons_of_mem _ hx)) hN)]
      · rfl

theorem eW_wordRed : ∀ (w : List ℤ), (∀ y ∈ w, LOK NW KA KB y) → ∀ {N : Nat}, N < 920808 →
    eW NW KA KB (wordRed w) N = eW NW KA KB w N
  | [], _, _, _ => rfl
  | z :: w, h, N, hN => by
    have ht : ∀ y ∈ w, LOK NW KA KB y := fun y hy => h y (List.mem_cons_of_mem z hy)
    change eW NW KA KB (freeStep z (wordRed w)) N = _
    rw [eW_freeStep (h z List.mem_cons_self) (fun y hy => ht y (wordRed_sub w y hy)) hN, eW_wordRed w ht hN,
      eW_cons]

def followsOK (K : List (List ℤ)) (v : List ℤ) (k : Nat) : Bool :=
  decide (wordRed v = []) || (List.range (K.getD k []).length).any fun r =>
    decide (v = wordRot r (K.getD k [])) || decide (v = wordRot r (wordInv (K.getD k [])))

theorem followsOK_spec {K : List (List ℤ)} {v : List ℤ} {k : Nat} (hv : ∀ z ∈ v, LOK NW KA KB z)
    (hu : ∀ z ∈ K.getD k [], LOK NW KA KB z) (hU : ∀ N < 920808, eW NW KA KB (K.getD k []) N = N)
    (h : followsOK K v k = true) : ∀ N < 920808, eW NW KA KB v N = N := by
  intro N hN
  simp only [followsOK, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨r, -, h | h⟩
  · rw [← eW_wordRed v hv hN, h]
    rfl
  · rw [h]
    exact eW_wordRot hu hU r N hN
  · rw [h]
    exact eW_wordRot (wordInv_lok hu) (fun M hM => by
      have e := eW_wordInv _ hu M hM
      rwa [hU M hM] at e) r N hN

def followsAll (K T : List (List ℤ)) (I : List Nat) : Bool :=
  (List.range 64).all fun j => followsOK K (T.getD j []) (I.getD j 0)

theorem checked_id {K : List (List ℤ)} (hl : ∀ u ∈ K, ∀ z ∈ u, LOK NW KA KB z)
    (hc : ∀ g < 20 * K.length, Bool.rec (motive := fun _ => Bool)
      (idKOK NW KA KB (List.getD K (Nat.div g 20) [])) (idOK NW (List.getD K (Nat.div g 20) []) (Nat.mod g 20))
      (Nat.blt (Nat.mod g 20) 19) = true) (k : Nat) :
    (∀ z ∈ K.getD k [], LOK NW KA KB z) ∧ ∀ N < 920808, eW NW KA KB (K.getD k []) N = N := by
  by_cases hk : k < K.length
  · have hlk : ∀ z ∈ K.getD k [], LOK NW KA KB z := by
      rw [List.getD_eq_getElem _ _ hk]
      exact hl _ (List.getElem_mem hk)
    refine ⟨hlk, id_spec hlk (fun j hj => ?_) ?_⟩
    · have h := hc (20 * k + j) (by omega)
      have e1 : Nat.mod (20 * k + j) 20 = j := by change (20 * k + j) % 20 = j; omega
      have e2 : Nat.div (20 * k + j) 20 = k := by change (20 * k + j) / 20 = k; omega
      rw [e1, e2, Nat.blt_eq.mpr hj] at h
      exact h
    · have h := hc (20 * k + 19) (by omega)
      have e1 : Nat.mod (20 * k + 19) 20 = 19 := by change (20 * k + 19) % 20 = 19; omega
      have e2 : Nat.div (20 * k + 19) 20 = k := by change (20 * k + 19) / 20 = k; omega
      rw [e1, e2, show Nat.blt 19 19 = false from rfl] at h
      exact h
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨fun z hz => absurd hz List.not_mem_nil, fun N _ => rfl⟩

theorem eW_followsAll {K T : List (List ℤ)} {I : List Nat}
    (hK : ∀ k, (∀ z ∈ K.getD k [], LOK NW KA KB z) ∧ ∀ N < 920808, eW NW KA KB (K.getD k []) N = N)
    (hd : followsAll K T I = true) {j : Nat} (hj : j < 64) (hv : ∀ z ∈ T.getD j [], LOK NW KA KB z) :
    ∀ N < 920808, eW NW KA KB (T.getD j []) N = N := by
  unfold followsAll at hd
  rw [List.all_eq_true] at hd
  exact followsOK_spec hv (hK _).1 (hK _).2 (hd j (List.mem_range.2 hj))

end Derive

theorem qw_slice {a i : Nat} (ha : a + 64 ≤ 256) (h0 : a ≤ i) (hi : i < a + 64) :
    (((relsQ.drop a).take 64).map (List.map cq)).getD (i - a) [] = qw i := by
  have hi0 : i < relsQ.length := by rw [relsQ_length]; omega
  unfold qw
  rw [getElem!_pos relsQ i hi0]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_sub_cancel' h0,
    List.getElem?_eq_getElem hi0, (by omega : i - a < 64)]

theorem eW_qwT {T K : List (List Int)} {I : List Nat} {a : Nat} (ha : a + 64 ≤ 256)
    (hT : T = ((relsQ.drop a).take 64).map (List.map cq)) (hKl : ∀ u ∈ K, ∀ z ∈ u, z.natAbs - 1 < 42)
    (hc : ∀ g < 20 * K.length, qckT K g = true) (hd : followsAll K T I = true)
    {i : Nat} (h0 : a ≤ i) (hi : i < a + 64) : ∀ N < 920808, eW NWP KAP KBP (qw i) N = N := by
  have hq : T.getD (i - a) [] = qw i := by
    subst hT
    exact qw_slice ha h0 hi
  have hl := qw_letters (by omega : i < 256)
  have hK := checked_id (fun u hu z hz => lokP (hKl u hu z hz)) (fun g hg => by
    have h := hc g hg
    unfold qckT at h
    exact h)
  rw [← hq]
  exact eW_followsAll hK hd (by omega) (by rw [hq]; exact fun z hz => lokP (hl z hz))

theorem qkT0_letters : ∀ u ∈ qkT0, ∀ z ∈ u, z.natAbs - 1 < 42 := by decide +kernel

theorem qkT1_letters : ∀ u ∈ qkT1, ∀ z ∈ u, z.natAbs - 1 < 42 := by decide +kernel

theorem qkT2_letters : ∀ u ∈ qkT2, ∀ z ∈ u, z.natAbs - 1 < 42 := by decide +kernel

theorem qiT0_ok : followsAll qkT0 (((relsQ.drop 0).take 64).map (List.map cq)) qiT0 = true := by
  decide +kernel

theorem qiT1_ok : followsAll qkT1 (((relsQ.drop 64).take 64).map (List.map cq)) qiT1 = true := by
  decide +kernel

theorem qiT2_ok : followsAll qkT2 (((relsQ.drop 128).take 64).map (List.map cq)) qiT2 = true := by
  decide +kernel

theorem qw_243 : qw 243 = (List.replicate 17 wU3).flatten ++ [42] := by decide +kernel

theorem qkT3_letters : ∀ u ∈ qkT3, ∀ z ∈ u, z.natAbs - 1 < 43 := by decide +kernel

theorem qiT3_ok : followsAll qkT3 ((((relsQ.drop 192).take 64).map (List.map cq)).set 51 []) qiT3 = true := by
  decide +kernel

theorem qkT3_id (k : Nat) : (∀ z ∈ qkT3.getD k [], LOK NWU3 KAU3 KBU3 z) ∧
    ∀ N < 920808, eW NWU3 KAU3 KBU3 (qkT3.getD k []) N = N :=
  checked_id (fun u hu z hz => lokU3 (qkT3_letters u hu z hz)) qckU3_all k

theorem eW_qwU3 {i : Nat} (h0 : 192 ≤ i) (hi : i < 256) (h243 : i ≠ 243) :
    ∀ N < 920808, eW NWU3 KAU3 KBU3 (qw i) N = N := by
  have hne : 51 ≠ i - 192 := by omega
  have hq : ((((relsQ.drop 192).take 64).map (List.map cq)).set 51 []).getD (i - 192) [] = qw i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
    exact qw_slice (by decide) h0 (by omega)
  have hl := qw_letters hi
  rw [← hq]
  exact eW_followsAll qkT3_id qiT3_ok (by omega) (by rw [hq]; exact fun z hz => lokU3 (by have := hl z hz; omega))

theorem eW_qw {i : Nat} (hi : i < 256) : ∀ N < 920808, eW NWP KAP KBP (qw i) N = N := by
  have hl := qw_letters hi
  by_cases h192 : i < 192
  · by_cases h64 : i < 64
    · exact eW_qwT (a := 0) (by decide) rfl qkT0_letters qck0_all qiT0_ok (by omega) (by omega)
    by_cases h128 : i < 128
    · exact eW_qwT (a := 64) (by decide) rfl qkT1_letters qck1_all qiT1_ok (by omega) (by omega)
    · exact eW_qwT (a := 128) (by decide) rfl qkT2_letters qck2_all qiT2_ok (by omega) (by omega)
  · rw [← eW_U3 _ fun z hz => by have := hl z hz; omega]
    by_cases h243 : i = 243
    · subst h243
      have e : qkT3.getD 15 [] = List.replicate 17 43 ++ [42] := rfl
      have hU := (qkT3_id 15).2
      rw [e] at hU
      intro N hN
      rw [qw_243, ← eW_replicate eL_U3 (fun z hz => lokU3 (by have := wU3_letters z hz; omega))
        (fun z hz => lokU3 (by revert z; decide)) 17 hN]
      exact hU N hN
    · exact eW_qwU3 (by omega) hi h243

theorem wordG_relsQ {w : List ℤ} (hw : w ∈ relsQ) : wordG (letterPerm gq 22) w = 1 := by
  obtain ⟨i, hi0, rfl⟩ := List.mem_iff_getElem.1 hw
  have hi : i < 256 := by rw [← relsQ_length]; exact hi0
  have hq : qw i = (relsQ[i]'hi0).map cq := by
    unfold qw
    rw [getElem!_pos relsQ i hi0]
  have hlet := relsQ_letters _ hw
  apply Equiv.ext
  intro y
  apply Fin.ext
  rw [wordG_apply (NW := NWP) (KA := KAP) (KB := KBP) _ cq _ (fun l hl y => letterPerm_act (hlet l hl) y) y,
    ← hq, eW_qw hi _ y.isLt]
  rfl

theorem genTabs_size : (genTabs ()).size = 22 := by simp [genTabs, xTabs, zTabs]

theorem relatorsOK_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    relatorsOK degree (genTabs ()) ((genTabs ()).map (invT degree))
      (wsQ.map fun (w : List (Fin nG × Bool)) => w.map litI) = true := by
  have hrep := genTabs_rep_of hm
  unfold relatorsOK
  rw [List.all_eq_true, wsQ_eq]
  intro w hw
  have h1 := rep_wordT_letters (G := Perm Pt) (n := 920808) hn32 (gs := genTabs ()) (π := gq)
    (fun l hl => hrep l (by rw [genTabs_size] at hl; exact hl))
    (fun l hl => invOK_invT_of_rep hn32 (hrep l (by rw [genTabs_size] at hl; exact hl))) w
  rw [genTabs_size, wordG_relsQ hw] at h1
  exact eqTab_of_rep h1 (Rep.idT hn32)

theorem ap_genTabs (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1))
    {i x : Nat} (hi : i < 22) (hx : x < 920808) : ap (genTabs ())[i]! x = (gq i ⟨x, hx⟩).val := by
  rw [genTabs_rep_of hm i hi x hx, idx_of_lt _ hx, Perm.smul_def]

theorem fixOK_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    fixOK (genTabs ()) = true := by
  unfold fixOK
  rw [List.all_eq_true]
  intro i hi
  have key : ∀ j < 10, (gq ([0, 1, 2, 3, 4, 5, 6, 7, 9, 10] : List Nat)[j]! ⟨0, by decide⟩).val = 0 := by
    intro j hj
    have hf := fixck_all j hj
    unfold fixck at hf
    have hz : zpL[j]! = cq ((([0, 1, 2, 3, 4, 5, 6, 7, 9, 10] : List Nat)[j]! + 1 : Nat) : ℤ) := by
      interval_cases j <;> decide
    rw [hz] at hf
    have hw : ∀ z ∈ [cq ((([0, 1, 2, 3, 4, 5, 6, 7, 9, 10] : List Nat)[j]! + 1 : Nat) : ℤ)],
        LOK NWP KAP KBP z := by
      intro z hz'
      rw [List.mem_singleton] at hz'
      subst hz'
      exact lokP (by interval_cases j <;> decide)
    have := ptOK_spec hw (by decide) (by decide) hf
    rw [eW_cons] at this
    rw [(gq_act (by interval_cases j <;> decide) _).1]
    exact this
  simp only [List.mem_cons, List.not_mem_nil] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h
  all_goals first
    | (rw [beq_iff_eq, ap_genTabs hm (by decide) (by decide)]; first
        | exact key 0 (by decide) | exact key 1 (by decide) | exact key 2 (by decide)
        | exact key 3 (by decide) | exact key 4 (by decide) | exact key 5 (by decide)
        | exact key 6 (by decide) | exact key 7 (by decide) | exact key 8 (by decide)
        | exact key 9 (by decide))
    | exact absurd h id

theorem moveOK_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    moveOK (genTabs ()) = true := by
  unfold moveOK
  rw [bne_iff_ne, ne_eq, ap_genTabs hm (by decide) (by decide)]
  have h := rep_shift 0 (by decide)
  rw [idx_of_lt _ (by decide), Perm.smul_def, ap_ofFn _ (by decide)] at h
  have e : gq 21 = gP 41 := rfl
  rw [e, ← h]
  decide

theorem bgLines_factors : ∀ ℓ < 4, ∀ p ∈ pairsOf (bridgeGensLinesK.toArray[ℓ]!), p.1 ≤ 13 := by
  decide +kernel

theorem slpOK_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    slpOK degree ((genTabs ()).extract 0 11) (mTabs ()) = true := by
  have hrep := genTabs_rep_of hm
  have hls : (slpLines bridgeGensText).size = 4 := bridgeGensLines_size
  have hxs : ((genTabs ()).extract 0 11).size = 11 := by simp [genTabs_size]
  set regsG : ℕ → Perm Pt := fun r => if r < 11 then gP (28 + r) else 1
  set regs := (genTabs ()).extract 0 11 ++ Array.replicate ((slpLines bridgeGensText).size + 1) (idT degree)
  have hrs : regs.size = 16 := by simp [regs, hxs, hls]
  have hregs : ∀ r < regs.size, Rep 920808 regs[r]! (regsG r) := by
    intro r hr
    rw [hrs] at hr
    by_cases h11 : r < 11
    · have e : regs[r]! = (genTabs ())[r]! := by
        rw [getElem!_pos _ r (by rw [hrs]; omega), Array.getElem_append_left (by rw [hxs]; exact h11),
          getElem!_pos (genTabs ()) r (by rw [genTabs_size]; omega)]
        simp
      rw [e]
      have := hrep r (by omega)
      have eg : gq r = gP (28 + r) := ite_eq_left h11
      simp only [regsG, ite_eq_left h11]
      rwa [eg] at this
    · have e : regs[r]! = idT degree := by
        rw [getElem!_pos _ r (by rw [hrs]; omega), Array.getElem_append_right (by rw [hxs]; omega)]
        simp
      rw [e]
      simp only [regsG, ite_eq_right h11]
      exact Rep.idT hn32
  have hprog : ∀ ins ∈ compileSLP 11 (slpLines bridgeGensText), instrRegsLt regs.size ins := by
    have := bridgeGensProg_ok
    rw [show 11 + (slpLines bridgeGensText).size + 1 = regs.size by rw [hrs, hls]] at this
    exact instrRegsLt_of_progOK' this
  obtain ⟨hflag, -, hres⟩ := runSLP_rep' hn32 _ regs regsG hprog hregs
  have hlines := prog_spec (NW := NWP) (KA := KAP) (KB := KBP) (g := 11) (o := 28)
    (ls := slpLines bridgeGensText) (t := bgT) bridgeGensLines_linesOK (regs := regsG)
    (fun r hr => by simp only [regsG, ite_eq_left hr]; rw [Nat.add_comm])
    (fun ℓ hℓ => lokP (by rw [hls] at hℓ; unfold bgT; interval_cases ℓ <;> decide))
    (fun ℓ hℓ z hz => by
      rw [bridgeGensLines_eq] at hz
      unfold lineW at hz
      obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
      have h1 := bgLines_factors ℓ (by rw [hls] at hℓ; exact hℓ) p (List.mem_reverse.1 hp)
      have := (List.mem_replicate.1 hz).2
      refine lokP ?_
      split_ifs at this <;> subst this <;> simp <;> omega)
    (fun ℓ hℓ k hk => by
      rw [bridgeGensLines_eq]
      exact (lineOK_spec (fun k' hk' => by
        have h : 20 * ℓ + k' < 80 := by rw [hls] at hℓ; omega
        exact bgck_all (20 * ℓ + k') h)).1 k hk)
    (fun ℓ hℓ => by
      rw [bridgeGensLines_eq]
      exact (lineOK_spec (fun k' hk' => by
        have h : 20 * ℓ + k' < 80 := by rw [hls] at hℓ; omega
        exact bgck_all (20 * ℓ + k') h)).2)
    (fun ℓ hℓ p hp hgp => by
      have h1 := bgLines_factors ℓ (by rw [hls] at hℓ; exact hℓ) p (by rw [← bridgeGensLines_eq]; exact hp)
      unfold bgT
      rcases (by omega : p.1 = 12 ∨ p.1 = 13) with h | h <;> rw [h] <;> rfl)
  have e13 := hlines 2 (by rw [hls]; decide)
  have e14 := hlines 3 (by rw [hls]; decide)
  unfold slpOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨hxs, by rw [hrs]; decide⟩, ?_⟩, hflag⟩, rfl⟩, ?_⟩, ?_⟩
  · have := bridgeGensProg_ok
    rwa [show 11 + (slpLines bridgeGensText).size + 1 = regs.size by rw [hrs, hls]] at this
  · have h := hres 13 (by rw [hrs]; decide)
    rw [show (13 : Nat) = 11 + 2 from rfl, e13] at h
    exact eqTab_of_rep h hm.1
  · have h := hres 14 (by rw [hrs]; decide)
    rw [show (14 : Nat) = 11 + 3 from rfl, e14] at h
    exact eqTab_of_rep h hm.2

theorem treeCheck_of_trans (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    treeCheck degree (mTabs ())[0]! (mTabs ())[1]! = true := by
  have hg : ∀ z ∈ ([-1, -2] : List ℤ), LOK NWP KAP KBP z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl <;> exact lokP (by decide)
  obtain ⟨-, -, hmin, hcnt⟩ := orb_spec (by decide) hg BridgeCk.trans
  have hall : ∀ N < 920808, memS (closeS NWP KAP KBP [-1, -2] 62 (single 0)) N = true := by
    have := List.length_filter_eq_length_iff.1 (by rw [hcnt, List.length_range])
    exact fun N hN => this N (List.mem_range.2 hN)
  have hap0 : ∀ x (hx : x < 920808), ap (mTabs ())[0]! x = eL NWP KAP KBP (Int.negSucc 0) x := by
    intro x hx
    rw [hm.1 x hx, idx_of_lt _ hx, Perm.smul_def, gT_apply (lokP (by decide))]
  have hap1 : ∀ x (hx : x < 920808), ap (mTabs ())[1]! x = eL NWP KAP KBP (Int.negSucc 1) x := by
    intro x hx
    rw [hm.2 x hx, idx_of_lt _ hx, Perm.smul_def, gT_apply (lokP (by decide))]
  have heL : ∀ (z : ℤ) (x : Nat), ¬ x < 920808 → eL NWP KAP KBP z x = x := by
    intro z x hx
    unfold eL
    rw [ite_eq_right hx]
  refine treeCheck_of (by decide) (by decide) (fun x hx => ?_) (fun x hx => ?_) ?_
  · rw [hap0 x hx]
    exact eL_lt (hg _ (by simp)) hx
  · rw [hap1 x hx]
    exact eL_lt (hg _ (by simp)) hx
  · intro P hP0 hP x hx
    refine hmin P hP0 (fun N hN z hz => ?_) x hx (hall x hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases hN' : N < 920808
    · rcases hz with rfl | rfl
      · have := (hP N hN).1
        rwa [hap0 N hN'] at this
      · have := (hP N hN).2
        rwa [hap1 N hN'] at this
    · rw [heL z N hN']
      exact hN

theorem bridgeOKAt_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    bridgeOKAt (genTabs ()) (mTabs ()) (wsQ.map fun (w : List (Fin nG × Bool)) => w.map litI) = true := by
  have hrep := genTabs_rep_of hm
  unfold bridgeOKAt
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨genTabs_size, rfl⟩, ?_⟩, ?_⟩, relatorsOK_of hm⟩, fixOK_of hm⟩, moveOK_of hm⟩,
    slpOK_of hm⟩, treeCheck_of_trans hm⟩
  · exact tabsOK_of_rep hn32 (fun i hi => hrep i (by rw [genTabs_size] at hi; exact hi))
  · refine tabsOK_of_rep hn32 (gs := fun i => gP i) (fun i hi => ?_)
    have hi' : i < 2 := hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact hm.1
    · exact hm.2

end CertificateChecks.KernelRouteP

end
