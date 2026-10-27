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

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator CFSG.Sporadic.Recognition.Fi24PrimeMultiplier

#kc_forall_tree qck_all (fun g => CFSG.KD.RouteP.qck g = true) 5120 CFSG.KD.RouteP.BridgeCk.q
#kc_forall_tree fixck_all (fun j => CFSG.KD.RouteP.fixck j = true) 10 CFSG.KD.RouteP.BridgeCk.f

theorem gq_act {i : Nat} (hi : i < 22) (y : Pt) :
    (gq i y).val = eL NWP KAP KBP (cq ((i + 1 : Nat) : ℤ)) y.val ∧
      ((gq i)⁻¹ y).val = eL NWP KAP KBP (cq (-((i + 1 : Nat) : ℤ))) y.val := by
  by_cases h11 : i < 11
  · have eg : gq i = gP (28 + i) := if_pos h11
    have e1 : cq ((i + 1 : Nat) : ℤ) = Int.negSucc (28 + i) := by
      unfold cq
      rw [if_pos (by omega), if_pos (by omega), Int.negSucc_eq]
      omega
    have e2 : cq (-((i + 1 : Nat) : ℤ)) = Int.ofNat (28 + i + 1) := by
      unfold cq
      rw [if_pos (by omega), if_neg (by omega), Int.ofNat_eq_coe]
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
        rw [if_neg h11, if_neg h21]
      have e1 : cq ((i + 1 : Nat) : ℤ) = Int.ofNat 0 := by
        unfold cq
        rw [if_neg (by omega), if_neg (by omega)]
        rfl
      have e2 : cq (-((i + 1 : Nat) : ℤ)) = Int.ofNat 0 := by
        unfold cq
        rw [if_neg (by omega), if_neg (by omega)]
        rfl
      rw [eg, e1, e2, inv_one]
      exact ⟨(eL_zero NWP KAP KBP y.isLt).symm, (eL_zero NWP KAP KBP y.isLt).symm⟩

theorem letterPerm_act {l : ℤ} (hl : 1 ≤ l.natAbs ∧ l.natAbs ≤ 22) (y : Pt) :
    (letterPerm gq 22 l y).val = eL NWP KAP KBP (cq l) y.val := by
  unfold letterPerm
  by_cases hp : 0 < l
  · rw [if_pos ⟨hp, by omega⟩]
    have e : l = (((l - 1).toNat + 1 : Nat) : ℤ) := by omega
    conv_rhs => rw [e]
    exact (gq_act (by omega) y).1
  · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    have e : l = -(((-l - 1).toNat + 1 : Nat) : ℤ) := by omega
    conv_rhs => rw [e]
    exact (gq_act (by omega) y).2

theorem relsQ_length : relsQ.length = 256 := by decide +kernel

theorem relsQ_letters : ∀ w ∈ relsQ, ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 22 := by decide +kernel

theorem idOK_qw {i : Nat} (hi : i < 256) {k : Nat} (hk : k < 19) : idOK NWP (qw i) k = true := by
  have hlt : 20 * i + k < 5120 := by omega
  have h := qck_all (20 * i + k) hlt
  unfold qck at h
  have e1 : Nat.mod (20 * i + k) 20 = k := by change (20 * i + k) % 20 = k; omega
  have e2 : Nat.div (20 * i + k) 20 = i := by change (20 * i + k) / 20 = i; omega
  rw [e1, e2, Nat.blt_eq.mpr hk] at h
  exact h

theorem idKOK_qw {i : Nat} (hi : i < 256) : idKOK NWP KAP KBP (qw i) = true := by
  have hlt : 20 * i + 19 < 5120 := by omega
  have h := qck_all (20 * i + 19) hlt
  unfold qck at h
  have e1 : Nat.mod (20 * i + 19) 20 = 19 := by change (20 * i + 19) % 20 = 19; omega
  have e2 : Nat.div (20 * i + 19) 20 = i := by change (20 * i + 19) / 20 = i; omega
  rw [e1, e2, show Nat.blt 19 19 = false from rfl] at h
  exact h

theorem wordG_relsQ {w : List ℤ} (hw : w ∈ relsQ) : wordG (letterPerm gq 22) w = 1 := by
  obtain ⟨i, hi0, rfl⟩ := List.mem_iff_getElem.1 hw
  have hi : i < 256 := by rw [← relsQ_length]; exact hi0
  have hq : qw i = (relsQ[i]'hi0).map cq := by
    unfold qw
    rw [getElem!_pos relsQ i hi0]
  have hlet := relsQ_letters _ hw
  refine wordG_eq_one _ cq (fun l hl y => letterPerm_act (hlet l hl) y) ?_ ?_ ?_
  · intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    have := hlet l hl
    refine lokP ?_
    unfold cq
    split_ifs <;> omega
  · intro k hk
    rw [← hq]
    exact idOK_qw hi hk
  · rw [← hq]
    exact idKOK_qw hi

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
      have eg : gq r = gP (28 + r) := if_pos h11
      simp only [regsG, if_pos h11]
      rwa [eg] at this
    · have e : regs[r]! = idT degree := by
        rw [getElem!_pos _ r (by rw [hrs]; omega), Array.getElem_append_right (by rw [hxs]; omega)]
        simp
      rw [e]
      simp only [regsG, if_neg h11]
      exact Rep.idT hn32
  have hprog : ∀ ins ∈ compileSLP 11 (slpLines bridgeGensText), instrRegsLt regs.size ins := by
    have := bridgeGensProg_ok
    rw [show 11 + (slpLines bridgeGensText).size + 1 = regs.size by rw [hrs, hls]] at this
    exact instrRegsLt_of_progOK' this
  obtain ⟨hflag, -, hres⟩ := runSLP_rep' hn32 _ regs regsG hprog hregs
  have hlines := prog_spec (NW := NWP) (KA := KAP) (KB := KBP) (g := 11) (o := 28)
    (ls := slpLines bridgeGensText) (t := bgT) bridgeGensLines_linesOK (regs := regsG)
    (fun r hr => by simp only [regsG, if_pos hr]; rw [Nat.add_comm])
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
    rw [if_neg hx]
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
