module

public import Certificates.Kernel.Sp6Insp443.OrbGlue
public import Certificates.Kernel.Sp6Insp443.OrbSift
public import CFSG.GH74.Generic.S45.LEvSporSpec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelS6I

open CFSG.KS.Raw.Orb hiding tabP strictB_eq
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.Sp6I CFSG.KC.KGC31P
  CFSG.KC.BfsPin CFSG.KC.Child3 CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.SectionRank.QTK.Insp443.Sp6 CFSG.Quasithin.KGC31.Native CertificateChecks.KernelSpor
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem map_tabP {n w c : Nat} (hlt : ∀ i < n, pg w (mask w) c i < 2 ^ 32) :
    (tabP n w c).map UInt32.toNat = unpack n w c := by
  have hs : (unpack n w c).size = n := Array.size_ofFn
  refine Array.ext (by rw [Array.size_map, tabP_size, hs]) fun i h1 h2 => ?_
  have hi : i < n := hs ▸ h2
  rw [Array.getElem_map, ← getElem!_pos (tabP n w c) i (by rw [tabP_size]; exact hi),
    tabP_get hi, ← getElem!_pos (unpack n w c) i h2, CFSG.KC.Child3.unpack_get' hi,
    UInt32.toNat_ofNat',
    Nat.mod_eq_of_lt (hlt i hi)]

theorem siftOK_tabP {c : Nat} (hc : PP 36 6 c)
    (h : bAnd(Co3Text36.hiOK c, Co3Sp36.sift c) = true) : siftOK (tabP 36 6 c) = true := by
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨-, -, -, hlt⟩ := PF.canon_facts hc.1
  have hg := map_tabP (n := 36) (w := 6) (c := c) fun i hi => lt_trans (hlt i hi) (by norm_num)
  unfold siftOK co3Sp36Levels
  exact siftK_soundR Co3Sp36.binds Co3Sp36.perm Co3Sp36.hl hg (Nat.eq_of_beq_eq_true h.1)
    (allN_iff.2 fun i hi => Nat.blt_eq.mpr (hlt i hi)) h.2

theorem tabOK_tabP {c : Nat} (hc : PP 36 6 c) :
    tabOK 36 (tabP 36 6 c) (invT 36 (tabP 36 6 c)) = true := by
  have hn : (36 : Nat) < 2 ^ 32 := by norm_num
  have hT : Rep 36 (tabP 36 6 c) (CFSG.KC.HeGlueK.sg 36 6 c) := by
    rw [tabP_eq hc]
    exact rep_toTable hn _
  have hR := CFSG.GH74.Generic.S45.EvSpor.rep_invT_of_rep hn hT
  unfold tabOK
  refine allIn_eq_true.mpr fun i _ hi => ?_
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, hT i hi]
  refine ⟨idx_lt _ hi, ?_⟩
  rw [hR _ (idx_lt _ hi), idx_inv_idx]

theorem siftL_spec : ∀ {L : List Nat}, siftL L = true →
    ∀ c ∈ L, bAnd(Co3Text36.hiOK c, Co3Sp36.sift c) = true
  | [], _, _, h => absurd h List.not_mem_nil
  | d :: L, h, c, hc => by
    have h' : bAnd(Co3Text36.hiOK d, bAnd(Co3Sp36.sift d, siftL L)) = true := h
    rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hc with rfl | hc
    · rw [bAnd_eq, Bool.and_eq_true]
      exact ⟨h'.1, h'.2.1⟩
    · exact siftL_spec h'.2.2 c hc

theorem siftLL_spec : ∀ {C : List (List Nat)}, siftLL C = true →
    ∀ L ∈ C, ∀ c ∈ L, bAnd(Co3Text36.hiOK c, Co3Sp36.sift c) = true
  | [], _, _, h => absurd h List.not_mem_nil
  | d :: C, h, L, hL => by
    have h' : bAnd(siftL d, siftLL C) = true := h
    rw [bAnd_eq, Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hL with rfl | hL
    · exact siftL_spec h'.1
    · exact siftLL_spec h'.2 L hL

theorem cands_facts {C : List (List Nat)} (hC : ∀ c ∈ C, ∀ b ∈ c, PP 36 6 b)
    (hs : siftLL C = true) :
    candsOK 36 (C.map (List.map (tabP 36 6))) = true ∧
      ((C.map (List.map (tabP 36 6))).all fun c => c.all siftOK) = true := by
  unfold candsOK
  simp only [List.all_map, List.all_eq_true, Function.comp_apply]
  exact ⟨fun c hc b hb => tabOK_tabP (hC c hc b hb),
    fun c hc b hb => siftOK_tabP (hC c hc b hb) (siftLL_spec hs c hc b hb)⟩

theorem chkOrb_true :
    chkOrb () = true := by
  obtain ⟨⟨hc5, hce5⟩, ⟨hc7, hce7⟩, ⟨hx5, hxe5⟩, ⟨hx7, hxe7⟩, ho5, ho7⟩ := xfacts
  have hs := ch725105s
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at hs
  obtain ⟨hsx, hs5, hs7⟩ := hs
  have hsx5 := siftL_spec hsx O.X5 (by simp)
  have hsx7 := siftL_spec hsx O.X7 (by simp)
  obtain ⟨hk5, hf5⟩ := cands_facts hc5 hs5
  obtain ⟨hk7, hf7⟩ := cands_facts hc7 hs7
  have h5 := orb5
  have h7 := orb7
  rw [orderTables_eq_invs] at h5 h7
  unfold chkOrb
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, h5⟩, h7⟩
  · simp only [tabsOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    rw [hxe5, hxe7]
    exact ⟨tabOK_tabP hx5, tabOK_tabP hx7⟩
  · rw [hxe5]
    exact siftOK_tabP hx5 hsx5
  · rw [hxe7]
    exact siftOK_tabP hx7 hsx7
  · rw [hxe5, ordTest_tabP hx5]
    exact ho5
  · rw [hxe7, ordTest_tabP hx7]
    exact ho7
  · rw [hce5]
    exact hk5
  · rw [hce7]
    exact hk7
  · rw [hce5]
    exact hf5
  · rw [hce7]
    exact hf7

end CertificateChecks.KernelS6I

end
