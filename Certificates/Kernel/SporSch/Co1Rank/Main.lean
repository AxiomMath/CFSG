module

public import Certificates.Kernel.SporSch.Co1Rank.ChkGen
public import Certificates.Kernel.SporSch.Co1Rank.RecB
public import Certificates.Kernel.SporSch.Co1Rank.RecC
public import Certificates.Kernel.SporSch.Co1Rank.BndB
public import Certificates.Kernel.SporSch.Co1Rank.BndC
public import Certificates.Kernel.SporSch.Co1.Packed
public import Certificates.Kernel.Co1B.Iota
public import CFSG.Certificates.Kernel.SporSch.Co1RankMainSound
public import CFSG.Certificates.Kernel.SporSch.Co1HeisSound
public import CFSG.Certificates.Kernel.SporSch.Co1CentSound

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1RankGen

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.KC.Co1Cl CFSG.KC.Co1RankCoord CFSG.KS.SporSch.Co1Rank
  CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic CertificateChecks.KernelSporSch.Co1Packed
  CFSG.KC.Co1RankRec

@[expose] noncomputable def gensB (g : ℕ) : GL24 := (dagG [A₁, A₂] rankBD).getD (rankBIdx.getD g 0) 1

@[expose] noncomputable def gensC (g : ℕ) : GL24 :=
  (dagG (brayEltsG cG twoCD1 twoCBray) rankCD2).getD (rankCIdx.getD g 0) 1

theorem matK_of_rep {X : ℕ} {g : GL24} (h : MRep (unpack 24 24 X) g) :
    matK X = (g : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  rw [← unpackR_eq_unpack] at h
  exact (mRep_iff X g).1 h

theorem matK_dag {base : List Native.Rows} {baseG : List GL24} (hb : List.Forall₂ MRep base baseG)
    (derivs : List (List ℤ)) {M MI : ℕ → ℕ} {N : ℕ}
    (hD : Native.dag base derivs = ((List.range N).map fun i => unpack 24 24 (M i),
      (List.range N).map fun i => unpack 24 24 (MI i), true)) {j : ℕ} (hj : j < N) :
    matK (M j) = ((dagG baseG derivs).getD j 1 : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have hflag : (Native.dag base derivs).2.2 = true := by rw [hD]
  have hrep := getD_rep (dag_rep hb derivs hflag) MRep.one j
  rw [hD] at hrep
  change MRep (((List.range N).map fun i => unpack 24 24 (M i)).getD j (Native.one ())) _ at hrep
  rw [getD_range_unpack hj] at hrep
  exact matK_of_rep hrep

theorem baseB : [Native.aR, Native.bR] = (List.range 2).map fun i => unpack 24 24 (RB.M i) := by
  have h := kbB
  simp only [Bool.and_eq_true] at h
  have hr : List.range 2 = [0, 1] := rfl
  have ha : PA = CFSG.KD.Co1B.SA := rfl
  have hb : PB = CFSG.KD.Co1B.SB := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_nil, aR_u, bR_u, Nat.eq_of_beq_eq_true h.1,
    Nat.eq_of_beq_eq_true h.2, ha, hb]

theorem dagB_eq : Native.dag [Native.aR, Native.bR] rankBD =
    ((List.range RB.N).map fun i => unpack 24 24 (RB.M i),
      (List.range RB.N).map fun i => unpack 24 24 (RB.MI i), true) := by
  have h := dagWK_sound baseB kDB
  rwa [decWords_encWordK] at h

theorem partsB : Co1RankTabB.nG = 6 ∧ (∀ j ∈ rankBIdx, j < RB.N) ∧
    (∀ g < 6, CFSG.KC.Co1RankTab.getM Co1RankTabB.G g = RB.M (rankBIdx.getD g 0)) ∧
    Co1RankTabB.cM = CFSG.KD.Co1B.SA ∧ Co1RankTabB.BS.length = Co1RankTabB.d := by
  have h := kGB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, h2, fun g hg => Nat.eq_of_beq_eq_true (h3 g ?_),
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩
  exact List.mem_range.2 hg

theorem hGB : ∀ g < Co1RankTabB.dat.nG,
    matK (CFSG.KC.Co1RankTab.getM Co1RankTabB.dat.G g) = (gensB g : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  intro g hg
  change g < Co1RankTabB.nG at hg
  rw [partsB.1] at hg
  change matK (CFSG.KC.Co1RankTab.getM Co1RankTabB.G g) = _
  rw [partsB.2.2.1 g hg]
  have hj : rankBIdx.getD g 0 ∈ rankBIdx := by
    rw [List.getD_eq_getElem _ _ (by simpa [rankBIdx] using hg)]
    exact List.getElem_mem _
  exact matK_dag (.cons rep_A₁ (.cons rep_A₂ .nil)) rankBD dagB_eq (partsB.2.1 _ hj)

theorem iotaC_u : iotaCRows = unpack 24 24 IC :=
  CertificateChecks.KernelCo1B.iotaC_eq.trans (unpackR_eq_unpack _)

theorem baseC : [Native.aR, Native.bR, iotaCRows] =
    (List.range 3).map fun i => unpack 24 24 (C1.M i) := by
  have h := kbC
  simp only [Bool.and_eq_true] at h
  have hr : List.range 3 = [0, 1, 2] := rfl
  have ha : PA = CFSG.KD.Co1B.SA := rfl
  have hb : PB = CFSG.KD.Co1B.SB := rfl
  rw [hr, List.map_cons, List.map_cons, List.map_cons, List.map_nil, aR_u, bR_u, iotaC_u,
    Nat.eq_of_beq_eq_true h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2, ha, hb]

theorem dagC1_eq : brayRows iotaCRows twoCD1 =
    ((List.range C1.N).map fun i => unpack 24 24 (C1.M i),
      (List.range C1.N).map fun i => unpack 24 24 (C1.MI i), true) := by
  have h := dagWK_sound baseC kDC1
  rwa [decWords_encWordK] at h

theorem brayC : brayElts (brayRows iotaCRows twoCD1) twoCBray =
    (List.range twoCBray.length).map fun i => unpack 24 24 (C2.M i) := by
  have hj : ∀ j ∈ twoCBray, 3 < j ∧ j ≤ C1.N := fun j hj => by
    simpa using List.all_eq_true.1 kIC j hj
  have hbi : ∀ (i : Nat) (hi : i < twoCBray.length), C2.M i = C1.M (twoCBray[i] - 1) :=
    fun i hi => by simpa using bindFromK_sound (k := 0) kBindC i hi
  rw [dagC1_eq]
  apply List.ext_getElem (by simp [brayElts])
  intro i h₁ h₂
  simp only [brayElts, List.length_map] at h₁
  simp only [brayElts, List.getElem_map, List.getElem_range]
  have := hj _ (List.getElem_mem h₁)
  rw [getD_range_unpack (by omega), ← hbi i h₁]

theorem dagC2_eq : Native.dag (brayElts (brayRows iotaCRows twoCD1) twoCBray) rankCD2 =
    ((List.range C2.N).map fun i => unpack 24 24 (C2.M i),
      (List.range C2.N).map fun i => unpack 24 24 (C2.MI i), true) := by
  have h := dagWK_sound brayC kDC2
  rwa [decWords_encWordK] at h

theorem partsC : Co1RankTabC.nG = rankCIdx.length ∧ (∀ j ∈ rankCIdx, j < C2.N) ∧
    (∀ g < rankCIdx.length,
      CFSG.KC.Co1RankTab.getM Co1RankTabC.G g = C2.M (rankCIdx.getD g 0)) ∧
    Co1RankTabC.cM = IC ∧ Co1RankTabC.BS.length = Co1RankTabC.d := by
  have h := kGC
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨Nat.eq_of_beq_eq_true h1, h2, fun g hg => Nat.eq_of_beq_eq_true (h3 g ?_),
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩
  exact List.mem_range.2 hg

theorem hGC :
    ∀ g < Co1RankTabC.dat.nG,
    matK (CFSG.KC.Co1RankTab.getM Co1RankTabC.dat.G g) =
      (gensC g : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  intro g hg
  change g < Co1RankTabC.nG at hg
  rw [partsC.1] at hg
  change matK (CFSG.KC.Co1RankTab.getM Co1RankTabC.G g) = _
  rw [partsC.2.2.1 g hg]
  have hj : rankCIdx.getD g 0 ∈ rankCIdx := by
    rw [List.getD_eq_getElem _ _ hg]
    exact List.getElem_mem _
  have hflag : (brayRows iotaCRows twoCD1).2.2 = true := by rw [dagC1_eq]
  exact matK_dag (rep_brayElts rep_iotaC hflag) rankCD2 dagC2_eq (partsC.2.1 _ hj)

theorem matK_SA :
    matK CFSG.KD.Co1B.SA = (A₁ : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have h := rep_A₁
  rw [aR_u] at h
  exact matK_of_rep h

theorem matK_IC :
    matK IC = (cG : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
  have h := rep_iotaC
  rw [iotaC_u] at h
  exact matK_of_rep h

theorem rank_ne :
    ((A₁ : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8 ∧
      ((cG : Matrix (Fin 24) (Fin 24) (ZMod 2)) - 1).rank ≠ 8 := by
  have hB := kRB
  have hC := kRC
  rw [rankRC_sound, matK_SA] at hB
  rw [rankRC_sound, matK_IC] at hC
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at hB
    exact absurd hB (by decide)
  · rw [h] at hC
    exact absurd hC (by decide)

theorem comm_of_matK {X Y : ℕ} {g t : GL24} (hX : matK X = (g : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    (hY : matK Y = (t : Matrix (Fin 24) (Fin 24) (ZMod 2)))
    (h : Nat.beq (CFSG.KC.Co1B.mulWK X Y) (CFSG.KC.Co1B.mulWK Y X) = true) : g * t = t * g := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, ← hX, ← hY, ← matK_mulWK, ← matK_mulWK,
    Nat.eq_of_beq_eq_true h]

theorem dims : Co1RankTabB.d = 8 ∧ Co1RankTabC.d = 11 := by
  have h := kdim
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem candB : ∀ n < 4, ∀ p ∈ getD [] Co1RankRecB.repsR n, ∃ C : CFSG.KC.Co1RankCand.Dat,
    CFSG.KC.Co1RankCand.chkC C = true ∧ CFSG.KC.Co1RankBnd.bndOK C = true ∧
      sameTab C Co1RankTabB.dat = true ∧ p ∈ C.reps := by
  have hb := Co1RankBndB.bnd_ok
  have hs := Co1RankRecB.sameTab_ok
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hb hs
  intro n hn p hp
  interval_cases n
  · exact ⟨_, Co1RankB1.chk_ok, hb.1, hs.1, hp⟩
  · exact ⟨_, Co1RankB2.chk_ok, hb.2.1, hs.2.1, hp⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact ⟨_, Co1RankB3a.chk_ok, hb.2.2.1, hs.2.2.1, hp⟩
    · exact ⟨_, Co1RankB3b.chk_ok, hb.2.2.2.1, hs.2.2.2.1, hp⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact ⟨_, Co1RankB4a.chk_ok, hb.2.2.2.2.1, hs.2.2.2.2.1, hp⟩
    · exact ⟨_, Co1RankB4b.chk_ok, hb.2.2.2.2.2, hs.2.2.2.2.2, hp⟩

theorem candC : ∀ n < 4, ∀ p ∈ getD [] Co1RankRecC.repsR n, ∃ C : CFSG.KC.Co1RankCand.Dat,
    CFSG.KC.Co1RankCand.chkC C = true ∧ CFSG.KC.Co1RankBnd.bndOK C = true ∧
      sameTab C Co1RankTabC.dat = true ∧ p ∈ C.reps := by
  have hb := Co1RankBndC.bnd_ok
  have hs := Co1RankRecC.sameTab_ok
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hb hs
  intro n hn p hp
  interval_cases n
  · exact ⟨_, Co1RankC1.chk_ok, hb.1, hs.1, hp⟩
  · exact ⟨_, Co1RankC2.chk_ok, hb.2.1, hs.2.1, hp⟩
  · rcases List.mem_append.1 hp with hp | hp
    · exact ⟨_, Co1RankC3a.chk_ok, hb.2.2.1, hs.2.2.1, hp⟩
    · rcases List.mem_append.1 hp with hp | hp
      · exact ⟨_, Co1RankC3b.chk_ok, hb.2.2.2.1, hs.2.2.2.1, hp⟩
      · exact ⟨_, Co1RankC3c.chk_ok, hb.2.2.2.2.1, hs.2.2.2.2.1, hp⟩
  · exact ⟨_, Co1RankC4.chk_ok, hb.2.2.2.2.2, hs.2.2.2.2.2, hp⟩

theorem rankB :
    Nat.card (Subgroup.closure (gensB '' {g | g < 6})) = 2 ^ 15 ∧
      (∀ g < 6, gensB g ∈ GA ∧ gensB g * A₁ = A₁ * gensB g) ∧
      ∀ B : Subgroup GL24, B ≤ Subgroup.closure (gensB '' {g | g < 6}) →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → A₁ ∈ B →
        (∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) → Nat.card B ≤ 16 := by
  have hn : Co1RankTabB.dat.nG = 6 := partsB.1
  have hbase : ∀ x ∈ [A₁, A₂], x ∈ GA := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h <;> rw [h]
    exacts [A₁_mem, A₂_mem]
  have hGA : ∀ g < Co1RankTabB.dat.nG, gensB g ∈ GA := fun g _ =>
    getD_mem_of_forall (dagG_mem hbase rankBD) _
  have hc : matK Co1RankTabB.dat.cM = (A₁ : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    change matK Co1RankTabB.cM = _
    rw [partsB.2.2.2.1, matK_SA]
  obtain ⟨h1, h2⟩ := card_le_of_tables rank_ne.1 rank_ne.2 Co1RankTabB.chkM_ok Co1RankTabB.chkT_ok
    Co1RankBndB.tab_ok partsB.2.2.2.2 Co1RankTabB.chkP_ok Co1RankRecB.chkR_ok candB hGB hGA hc
  rw [hn] at h1 h2
  have hd : Co1RankTabB.dat.d = 8 := dims.1
  rw [hd] at h1
  refine ⟨h1, fun g hg => ⟨hGA g (hn ▸ hg), ?_⟩, h2⟩
  have hk := List.all_eq_true.1 kCmB g (List.mem_range.2 hg)
  exact comm_of_matK (hGB g (hn ▸ hg)) matK_SA hk

theorem rankC :
    Nat.card (Subgroup.closure (gensC '' {g | g < rankCIdx.length})) = 2 ^ 18 ∧
      (∀ g < rankCIdx.length, gensC g ∈ GA ∧ gensC g * cG = cG * gensC g) ∧
      ∀ B : Subgroup GL24, B ≤ Subgroup.closure (gensC '' {g | g < rankCIdx.length}) →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → cG ∈ B →
        (∀ x ∈ B, x ≠ 1 → (xFix x).ncard ≠ 2280) → Nat.card B ≤ 16 := by
  have hn : Co1RankTabC.dat.nG = rankCIdx.length := partsC.1
  have hGA : ∀ g < Co1RankTabC.dat.nG, gensC g ∈ GA := fun g _ =>
    getD_mem_of_forall (dagG_mem (brayElts_mem_GA iotaC_mem_GA) rankCD2) _
  have hc : matK Co1RankTabC.dat.cM = (cG : Matrix (Fin 24) (Fin 24) (ZMod 2)) := by
    change matK Co1RankTabC.cM = _
    rw [partsC.2.2.2.1, matK_IC]
  obtain ⟨h1, h2⟩ := card_le_of_tables rank_ne.1 rank_ne.2 Co1RankTabC.chkM_ok Co1RankTabC.chkT_ok
    Co1RankBndC.tab_ok partsC.2.2.2.2 Co1RankTabC.chkP_ok Co1RankRecC.chkR_ok candC hGC hGA hc
  rw [hn] at h1 h2
  have hd : Co1RankTabC.dat.d = 11 := dims.2
  rw [hd] at h1
  refine ⟨h1, fun g hg => ⟨hGA g (hn ▸ hg), ?_⟩, h2⟩
  have hk := List.all_eq_true.1 kCmC g (List.mem_range.2 hg)
  exact comm_of_matK (hGC g (hn ▸ hg)) matK_IC hk

end CFSG.KD.Co1RankGen

end
