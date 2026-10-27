module

public import Certificates.Kernel.RouteP.Lines.Rep
public import Certificates.Kernel.RouteP.Lines.PresL
public import Certificates.Kernel.RouteP.Bridge.Misc

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.KC.Fi24Net CFSG.KS.Fi24Net

#kc_forall_tree plckL_all (fun g => CFSG.KD.RouteP.plckL g = true) 740 CFSG.KD.RouteP.PresLC.p
#kc_forall_tree bgckL_all (fun g => CFSG.KD.RouteP.bgckL g = true) 80 CFSG.KD.RouteP.PresLC.b
#kc_forall_tree nkP_all (fun j => CFSG.KD.RouteP.nkP j = true) 42 CFSG.KD.RouteP.BridgeCk.n
#kc_forall_tree zck_all (fun k => CFSG.KD.RouteP.zck k = true) 20 CFSG.KD.RouteP.BridgeCk.z

theorem presW_eq : presLinesK = CFSG.KD.RouteP.PresW.PL :=
  eq_of_beq (by decide +kernel : (presLinesK == CFSG.KD.RouteP.PresW.PL) = true)

theorem bridgeGensW_eq : bridgeGensLinesK = CFSG.KD.RouteP.PresW.BL :=
  eq_of_beq (by decide +kernel : (bridgeGensLinesK == CFSG.KD.RouteP.PresW.BL) = true)

theorem plck_all : ∀ g < 740, CFSG.KD.RouteP.plck g = true := by
  intro g hg
  unfold CFSG.KD.RouteP.plck
  rw [presW_eq]
  exact plckL_all g hg

theorem bgck_all : ∀ g < 80, CFSG.KD.RouteP.bgck g = true := by
  intro g hg
  unfold CFSG.KD.RouteP.bgck
  rw [bridgeGensW_eq]
  exact bgckL_all g hg

noncomputable abbrev gP (j : Nat) : Perm Pt := gT NWP KAP KBP j

theorem lokP {z : ℤ} (hz : z.natAbs - 1 < 42) : LOK NWP KAP KBP z :=
  CFSG.KC.Benes.andB_true (nkP_all _ hz)

theorem presRun_rep (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    ∀ r < 39, Rep 920808 (runSLP degree (compileSLP 2 (slpLines presText ++ slpLines bridgeText))
      (mTabs () ++ Array.replicate ((slpLines presText ++ slpLines bridgeText).size + 1) (idT degree))).1[r]!
      (gP r) := by
  have hs := presLines_size
  intro r hr
  refine progRep_of presLines_eq rfl hm presProg_ok presLines_linesOK (fun j hj => lokP (by simp; omega))
    (fun ℓ hℓ z hz => lokP ?_) (fun g hg => plck_all g (by rw [hs] at hg; omega)) r (by rw [hs]; omega)
  rw [← presLines_eq] at hz
  unfold lineW at hz
  obtain ⟨p, hp, hz⟩ := List.mem_flatMap.1 hz
  have h1 := presLines_linesOK ℓ hℓ p (List.mem_reverse.1 hp)
  have := (List.mem_replicate.1 hz).2
  rw [hs] at hℓ
  split_ifs at this <;> subst this <;> simp <;> omega

@[expose] noncomputable def gq (i : Nat) : Perm Pt := if i < 11 then gP (28 + i) else if i = 21 then gP 41 else 1

theorem getElem!_map_range {α : Type} [Inhabited α] (f : Nat → α) {n i : Nat} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi)]
  simp

theorem rep_shift : Rep 920808 (Array.ofFn (n := degree) fun N =>
    UInt32.ofNat (3 * (N.val / 3) + (N.val % 3 + 2) % 3)) (gP 41) := by
  have hl : LOK NWP KAP KBP (Int.ofNat 42) := lokP (by decide)
  have hv : NV (NWP 41) := (net_spec hl.1).1
  have hid : ∀ q < 524288, pF (NWP 41) q = q := by
    have := wordP_spec (w := []) hv (fun z hz => absurd hz List.not_mem_nil) fun k hk => by
      have hk20 : k < 20 := by omega
      have e := zck_all k hk20
      unfold zck at e
      rw [Nat.blt_eq.mpr hk] at e
      exact e
    exact this
  have hR : ∀ q < 524288, pR (NWP 41) q = q := by
    intro q hq
    have := pR_pF hv q
    rwa [hid q hq] at this
  have h19 : (19 : Nat) < 20 := by decide
  have e19 := zck_all 19 h19
  unfold zck at e19
  have e19' : (Bool.rec false (Nat.beq (KBP 41) 0)
      (Nat.beq (KAP 41) (CFSG.KC.MonsterConv.Perm.ones 306936)) : Bool) = true := e19
  have ea : Nat.beq (KAP 41) (CFSG.KC.MonsterConv.Perm.ones 306936) = true := by
    cases h : Nat.beq (KAP 41) (CFSG.KC.MonsterConv.Perm.ones 306936)
    · rw [h] at e19'
      exact absurd e19' (by decide)
    · rfl
  have eb : Nat.beq (KBP 41) 0 = true := by
    rw [ea] at e19'
    exact e19'
  have hka := Nat.eq_of_beq_eq_true ea
  have hkb := Nat.eq_of_beq_eq_true eb
  intro N hN
  rw [idx_of_lt _ hN, Perm.smul_def, gT_apply hl, ap_ofFn _ hN,
    toNat_ofNat_of_lt (by change 3 * (N / 3) + (N % 3 + 2) % 3 < 2 ^ 32; omega)]
  unfold eL
  rw [if_pos hN]
  change _ = 3 * pR (NWP 41) (N / 3) + (N % 3 + (2 * kv (KAP 41) (KBP 41) (pR (NWP 41) (N / 3))) % 3) % 3
  rw [hR _ (by omega)]
  unfold kv
  rw [hka, hkb, testBit_onesW, decide_eq_true (by omega : N / 3 < 306936), Nat.zero_testBit]
  simp

theorem genTabs_rep_of (hm : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1)) :
    ∀ i < 22, Rep 920808 (genTabs ())[i]! (gq i) := by
  have hx : (xTabs ()).size = 11 := by simp [xTabs]
  have hz : (zTabs ()).size = 11 := by simp [zTabs]
  intro i hi
  unfold genTabs
  by_cases h11 : i < 11
  · rw [getElem!_pos _ i (by simp [hx, hz]; omega), Array.getElem_append_left (by rw [hx]; exact h11),
      ← getElem!_pos (xTabs ()) i (by rw [hx]; exact h11)]
    unfold xTabs
    simp only
    rw [getElem!_map_range _ h11]
    unfold gq
    rw [if_pos h11]
    exact presRun_rep hm (28 + i) (by omega)
  · rw [getElem!_pos _ i (by simp [hx, hz]; omega), Array.getElem_append_right (by rw [hx]; omega),
      ← getElem!_pos (zTabs ()) (i - (xTabs ()).size) (by rw [hx, hz]; omega), hx]
    unfold zTabs
    simp only
    rw [getElem!_map_range _ (by omega)]
    unfold gq
    rw [if_neg h11]
    by_cases h21 : i = 21
    · subst h21
      rw [if_pos rfl, if_pos rfl]
      exact rep_shift
    · rw [if_neg (by omega), if_neg h21]
      exact Rep.idT hn32

end CertificateChecks.KernelRouteP

end
