module

public import Certificates.Kernel.Sporadic.OddCore.ON2119A
public import CFSG.Sporadic.Schreier.ONPermArr

public section

namespace CertificateChecks.KernelSpor.ON2119

open CFSG.PSL3Four.Native CFSG.Sporadic.ONOddCore CFSG.ONSchreier CFSG.KC.Enum CFSG.KS
open CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.Misc.HexAt CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor.ON2129 CFSG.KC.BfsPin CFSG.ONSchreier.Native

theorem gens_size : Data.T32Chain.generators.size = 6 := (gensOK_of t32_gens).1

theorem inv_facts {j : Nat} (hj : j < 6) :
    invEqK 32 6 (mask 6) (32 * 6) (T32E.G j) (T32I j) = true ∧
      canonK 32 6 (mask 6) (32 * 6) (T32I j) = true ∧
      Nat.beq (pcomp 32 6 (mask 6) (T32I j) (T32E.G j)) (pidn 32 6) = true ∧
      Nat.beq (T32O.G j) (T32E.G j) = true ∧ Nat.beq (T32O.GI j) (T32I j) = true := by
  simpa only [bAnd_iff] using allN_spec inv_ok j hj

theorem gens_ok : GensOK 32 6 T32O.k T32O.G Data.T32Chain.generators := by
  refine ⟨gens_size, fun j hj => ?_⟩
  rw [Nat.eq_of_beq_eq_true (inv_facts hj).2.2.2.1]
  exact (gensOK_of t32_gens).2 j hj

theorem ginv_get {j : Nat} (hj : j < 6) :
    (Data.T32Chain.generators.map (invTab 32))[j]! = unpack 32 6 (T32I j) := by
  rw [getElem!_pos _ j (by simp [gens_size]; omega), Array.getElem_map,
    ← getElem!_pos _ j (by rw [gens_size]; omega), ((gensOK_of t32_gens).2 j hj).1]
  exact (invEqK_sound (inv_facts hj).1).1

theorem ginv_ok : GensOK 32 6 T32O.k T32O.GI (Data.T32Chain.generators.map (invTab 32)) := by
  refine ⟨by simp [gens_size]; rfl, fun j hj => ?_⟩
  have hj6 : j < 6 := hj
  rw [Nat.eq_of_beq_eq_true (inv_facts hj6).2.2.2.2]
  exact ⟨ginv_get hj6, (inv_facts hj6).2.1⟩

theorem invs32 : invsOK 32 Data.T32Chain.generators (Data.T32Chain.generators.map (invTab 32)) =
    true := by
  unfold invsOK allBelow
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨by simp, ?_⟩
  rw [all_range_iff]
  intro k hk
  have hk6 : k < 6 := by simpa [gens_size] using hk
  simp only [Bool.and_eq_true, beq_iff_eq]
  have hg := (gensOK_of t32_gens).2 k hk6
  rw [ginv_get hk6, hg.1]
  refine ⟨unpack_size _ _ _, ?_⟩
  rw [comp_unpack (inv_facts hk6).2.1 hg.2, idTab_eq,
    Nat.eq_of_beq_eq_true (inv_facts hk6).2.2.1]

theorem rep_eq {l : Nat} (hl : l < 7) : repTabs32[l]! = unpack 32 6 (T32O.R l) := by
  obtain ⟨hr, -⟩ := (bAnd_iff _ _).1 (allN_spec reps_ok l hl)
  rw [Nat.eq_of_beq_eq_true hr, lget2_eq]
  have hw : ∀ j ∈ repWords.toList.getD l [], Data.T32Chain.generators[j]! =
      unpack 32 6 (T32E.G j) ∧ canonK 32 6 (mask 6) (32 * 6) (T32E.G j) = true := by
    intro j hj
    have hj6 : j < 6 := by interval_cases l <;> simp [repWords] at hj <;> omega
    exact (gensOK_of t32_gens).2 j hj6
  have e : repTabs32[l]! = CFSG.Sporadic.SmallOddCore.wordTabS 32 Data.T32Chain.generators
      (repWords.toList.getD l []) := by
    rw [repTabs32, getElem!_pos _ l (by simp [repWords]; omega), Array.getElem_map]
    interval_cases l <;> rfl
  rw [e]
  exact (wordTabK_eq idTab_eq idCanon.1 _ hw).1

theorem orb_hd {l : Nat} (hl : l < 7) :
    penumHdK (T32O.R l) (T32O.C l) 64 (offF T32O.T (T32O.TO l)) (offF T32O.PL (T32O.PLO l)) =
      true :=
  ((bAnd_iff _ _).1 (allN_spec reps_ok l hl)).2

theorem orb_pt {l i : Nat} (hl : l < 7) (hi : i < T32O.C l) :
    penumPtK 32 6 (mask 6) (32 * 6) true T32O.G T32O.GI T32O.k (T32O.C l) (offF T32O.T (T32O.TO l))
      (offF T32O.PL (T32O.PLO l)) (offF T32O.POS (T32O.POSO l)) (offF T32O.SRT (T32O.SRTO l))
      (offF T32O.SRI (T32O.SRIO l)) i = true := by
  have hc : T32O.C l ≤ 64 := by
    have hh := orb_hd hl
    unfold penumHdK at hh
    exact Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 hh).2).1
  exact penumSl_spec (allN_spec orb_sl l hl) i (Nat.zero_le _) (by omega) hi

@[expose] noncomputable def orbRec (l : Nat) : Enum :=
  penumRec 32 6 (T32O.C l) (offF T32O.T (T32O.TO l)) (offF T32O.PL (T32O.PLO l))

theorem orb_enum {l : Nat} (hl : l < 7) : repOrbits32[l]! = orbRec l ∧
    treeOK (conjStep 32 Data.T32Chain.generators (Data.T32Chain.generators.map (invTab 32)))
      Data.T32Chain.generators.size repTabs32[l]! (orbRec l) = true := by
  have e : repOrbits32[l]! = orbitBFS 32 Data.T32Chain.generators
      (Data.T32Chain.generators.map (invTab 32)) repTabs32[l]! 64 := by
    rw [repOrbits32, getElem!_pos _ l (by simp [repTabs32, repWords]; omega), Array.getElem_map,
      ← getElem!_pos _ l (by simp [repTabs32, repWords]; omega)]
  rw [e]
  exact penumK_conj_sound szOK32 gens_ok ginv_ok (rep_eq hl) (orb_hd hl)
    (fun _ hi => orb_pt hl hi)

theorem t32_canon {k : Nat} (hk : k < T32E.cnt) : canonK 32 6 (mask 6) (32 * 6) (T32E.T k) = true :=
  penumPt_canon (t32_pt hk)

theorem classes2119 : invsOK 32 Data.T32Chain.generators
      (Data.T32Chain.generators.map (invTab 32)) = true ∧ repOrbits32.size = 7 ∧
    allBelowN 7 (fun i => orbitOK 32 Data.T32Chain.generators
      (Data.T32Chain.generators.map (invTab 32)) repTabs32[i]! repOrbits32[i]!) = true ∧
    coverOK 32 t32Enum.tabs (repOrbits32.map (·.tabs)) = true := by
  refine ⟨invs32, by simp [repOrbits32, repTabs32, repWords], ?_, ?_⟩
  · rw [allBelowN_iff]
    intro i hi
    unfold orbitOK
    rw [invs32, (orb_enum hi).1, (orb_enum hi).2]
    rfl
  · unfold coverOK allBelow
    rw [all_range_iff]
    intro k hk
    have hk' : k < T32E.cnt := by simpa [t32Enum_eq, penumRec] using hk
    have hc := allN_spec cover_ok k hk'
    unfold coverK at hc
    rw [strictB_app'] at hc
    rw [t32Enum_eq, rec_get hk']
    by_cases h0 : Nat.beq (T32COV k) 0 = true
    · rw [h0] at hc
      dsimp only at hc
      rw [idTab_eq, beq_unpack (t32_canon hk') idCanon.1, hc]
      rfl
    · rw [Bool.not_eq_true] at h0
      rw [h0] at hc
      by_cases h1 : Nat.beq (T32COV k) 1 = true
      · rw [h1] at hc
        dsimp only at hc
        rw [comp_unpack (t32_canon hk') (t32_canon hk'), idTab_eq,
          beq_unpack (canonK_pcomp (t32_canon hk') (t32_canon hk')) idCanon.1]
        cases he : Nat.beq (pcomp 32 6 (mask 6) (T32E.T k) (T32E.T k)) (pidn 32 6)
        · simp
        · rw [he] at hc
          exact absurd hc (by decide)
      · rw [Bool.not_eq_true] at h1
        rw [h1] at hc
        dsimp only at hc
        simp only [strictB_app'] at hc
        obtain ⟨hl, hq, he⟩ := (by simpa only [bAnd_iff] using hc :
          Nat.blt (Nat.shiftRight (Nat.sub (T32COV k) 2) 16) 7 = true ∧
          Nat.blt (Nat.land (Nat.sub (T32COV k) 2) 65535)
            (T32O.C (Nat.shiftRight (Nat.sub (T32COV k) 2) 16)) = true ∧
          Nat.beq (offF T32O.T (T32O.TO (Nat.shiftRight (Nat.sub (T32COV k) 2) 16))
            (Nat.land (Nat.sub (T32COV k) 2) 65535)) (T32E.T k) = true)
        have hl' := Eq.mp Nat.blt_eq hl
        have hfound : anyBelow (repOrbits32.map (·.tabs)).size (fun i =>
            found ((repOrbits32.map (·.tabs)).map indexOf)[i]! (repOrbits32.map (·.tabs))[i]!
              (unpack 32 6 (T32E.T k))) = true := by
          unfold anyBelow
          rw [List.any_eq_true]
          have hsz : Nat.shiftRight (Nat.sub (T32COV k) 2) 16 < (repOrbits32.map (·.tabs)).size := by
            simpa [repOrbits32, repTabs32, repWords] using hl'
          refine ⟨_, List.mem_range.2 hsz, ?_⟩
          rw [CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ hsz,
            CFSG.Sporadic.SmallOddCore.getElem!_map_eq _ _ (by simpa using hsz),
            (orb_enum hl').1]
          exact penum_found_sound (fun _ hx => orb_pt hl' hx) (Eq.mp Nat.blt_eq hq)
            (Nat.eq_of_beq_eq_true he)
        simp only [hfound, Bool.or_true]

end CertificateChecks.KernelSpor.ON2119

end
