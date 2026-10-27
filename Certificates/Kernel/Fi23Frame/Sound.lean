module

public import Certificates.Kernel.Fi23Frame.ChkDefs
public import Certificates.Kernel.Fi23Q.Regs
public import Certificates.Kernel.Fi23R.Group
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.FrameJHom
import Certificates.Kernel.Fi23Frame.Checks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Frame

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Frame CFSG.KD.Fi23K CFSG.KD.Fi23Frame
  CFSG.KS.Raw.Orb CFSG.Sporadic.Th CertificateChecks.KernelFi23R
  CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.Wong77.Module

@[expose] noncomputable def frP (i : ℕ) : CFSG.Sporadic.Fi23.J :=
  CFSG.Sporadic.Fi23.conjPt (frPts.getD i 0)

theorem frPts_lt (i : ℕ) : frPts.getD i 0 < 31671 := by
  have hall : ∀ x ∈ frPts, x < 31671 := by decide
  rw [List.getD_eq_getElem?_getD]
  cases h : frPts[i]? with
  | none => exact Nat.zero_lt_succ _
  | some x => exact hall x (List.mem_of_getElem? h)

theorem frW_cons (P : List ℕ) (i : ℕ) (L : List ℕ) :
    frW P (i :: L) = frW P L ++ [128 + P.getD i 0] := by
  unfold frW
  rw [List.map_cons, List.reverse_cons]
  try rfl

theorem frW_ok (L : List ℕ) : ∀ c ∈ frW frPts L, okL c := by
  intro c hc
  unfold frW at hc
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hc)
  have := frPts_lt i
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨Nat.le_add_right _ _, by
    change 128 + frPts.getD i 0 < 31799
    omega⟩)))

theorem prod_acts : ∀ L : List ℕ,
    ActsAs (CertificateChecks.KernelFi23Q.ρ (L.map frP).prod) (wa G (frW frPts L))
  | [] => fun x hx => by
    rw [List.map_nil, List.prod_nil, map_one]
    try rfl
  | i :: L => by
    have h1 : ActsAs (CertificateChecks.KernelFi23Q.ρ (frP i)) (tA G (frPts.getD i 0)) :=
      actsAs_congr (CertificateChecks.KernelFi23Q.ρ_acts _) fun x hx =>
        CertificateChecks.KernelFi23Q.conjPt_acts (frPts_lt i) x hx
    rw [List.map_cons, List.prod_cons, map_mul]
    refine actsAs_congr (h1.mul (prod_acts L)) fun x _ => ?_
    rw [frW_cons, wa_append, wa_cons, wa_nil, lf_eq, if_neg (by omega), Nat.add_sub_cancel_left]

theorem rho_inj {g h : CFSG.Sporadic.Fi23.J}
    (e : CertificateChecks.KernelFi23Q.ρ g = CertificateChecks.KernelFi23Q.ρ h) : g = h := by
  have h1 : h⁻¹ * g = 1 := CFSG.Sporadic.Fi23.eq_one_of_fix_all fun i => by
    have e' : g • i = h • i := congrArg (fun p : Equiv.Perm (Fin 31671) => p i) e
    rw [mul_smul, e', inv_smul_smul]
  exact (inv_mul_eq_one.1 h1).symm

theorem prod_eq_of_eqB {L M : List ℕ} (h : eqB G (frW frPts L) (frW frPts M) = true) :
    (L.map frP).prod = (M.map frP).prod := by
  have hw := wp_eq_of_eqB h (frW_ok L) (frW_ok M)
  have e1 := (prod_acts L).ext (wp_acts _ (frW_ok L))
  have e2 := (prod_acts M).ext (wp_acts _ (frW_ok M))
  exact rho_inj (by rw [e1, e2, hw])

theorem prod_ne_of_frNe {L M : List ℕ} (h : frNe G (frW frPts L) (frW frPts M) = true) :
    (L.map frP).prod ≠ (M.map frP).prod := by
  intro e
  have hB : eqB G (frW frPts L) (frW frPts M) = true := by
    unfold eqB
    refine allN_iff.2 fun b hb => ?_
    have hb' : b < 31671 := Nat.lt_of_lt_of_le hb (by decide)
    rw [← prod_acts L b hb', ← prod_acts M b hb', e, Nat.beq_eq]
  unfold frNe at h
  rw [hB] at h
  exact absurd h (by decide)

theorem beq_false {x y : ℕ} (h : x ≠ y) : ¬Nat.beq x y = true := fun e => h (Nat.eq_of_beq_eq_true e)

theorem prod_two (i j : ℕ) : ([i, j].map frP).prod = frP i * frP j := by
  rw [List.map_cons, List.map_cons, List.map_nil, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one]

theorem frame_comm (i j : Fin 23) : frP i * frP j = frP j * frP i := by
  have h := c24670comm_ok
  unfold c24670comm frComm at h
  have hc : ∀ i < 23, ∀ j < i, frP i * frP j = frP j * frP i := fun i hi j hj => by
    have h1 := allN_iff.1 (allN_iff.1 h i hi) j hj
    rw [← prod_two, ← prod_two]
    exact prod_eq_of_eqB h1
  rcases lt_trichotomy i.val j.val with hij | hij | hij
  · exact (hc j.val j.2 i.val hij).symm
  · rw [Fin.ext hij]
  · exact hc i.val i.2 j.val hij

theorem frame_trip (i j k : Fin 23) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    frP i * frP j ≠ frP k := by
  have hn : ∀ {x y : Fin 23}, x ≠ y → x.val ≠ y.val := fun h e => h (Fin.ext e)
  have hT : ∀ lo len, frTrip G frPts lo len = true → lo ≤ i.val → i.val < lo + len →
      frP i * frP j ≠ frP k := by
    intro lo len h h1 h2
    unfold frTrip at h
    have h3 := allN_iff.1 (allN_iff.1 (allN_iff.1 h (i.val - lo) (by omega)) j.val j.2) k.val k.2
    have e : Nat.add lo (i.val - lo) = i.val := by
      change lo + (i.val - lo) = i.val
      omega
    beta_reduce at h3
    rw [e] at h3
    unfold frTripAt at h3
    rw [bIf_eq, if_neg (beq_false (hn hij)), bIf_eq, if_neg (beq_false (hn hki)), bIf_eq,
      if_neg (beq_false (hn hkj))] at h3
    have h4 := prod_ne_of_frNe h3
    rw [prod_two] at h4
    rwa [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h4
  by_cases hi : i.val < 12
  · exact hT 0 12 c24670trip0_ok (Nat.zero_le _) (by omega)
  · exact hT 12 11 c24670trip1_ok (by omega) (by omega)

theorem rowList_eq : ∀ r : Fin 12,
    (rowList (golayMask r)).map Fin.val = frBits (frMasks.getD r.val 0) := by
  decide +kernel

theorem frame_rows (r : Fin 12) : ((rowList (golayMask r)).map fun i => frP i.val).prod = 1 := by
  have h := c24670rows_ok
  unfold c24670rows frRows at h
  have h1 := allN_iff.1 h r.val r.2
  have e : (rowList (golayMask r)).map (fun i => frP i.val) =
      (frBits (frMasks.getD r.val 0)).map frP := by
    rw [← rowList_eq, List.map_map]
    try rfl
  rw [e]
  exact prod_eq_of_eqB (M := []) h1

theorem frame_facts :
    (∀ i j : Fin 23, frP i * frP j = frP j * frP i) ∧
    (∀ i j k : Fin 23, i ≠ j → k ≠ i → k ≠ j → frP i * frP j ≠ frP k) ∧
    ∀ r : Fin 12, ((rowList (golayMask r)).map fun i => frP i.val).prod = 1 :=
  ⟨frame_comm, frame_trip, frame_rows⟩

end CertificateChecks.KernelFi23Frame

end
