module

public import Certificates.Kernel.MinusDerived.Checks3
public import Certificates.Kernel.MinusDerived.Facts2
public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedEnum
import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.LocalQTRestrSound
import CFSG.Certificates.Kernel.HeAutKLoops
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CertificateChecks.KernelMinusL

open CFSG.OddTranspositions.PartThree CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.Native CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native
  CFSG.QuasithinUnique.Id2519.HSAut
local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

@[expose] noncomputable def clsC : ClassData :=
  ⟨Array.ofFn (n := 7800) fun k => labK k.val, Array.ofFn (n := 15) fun l => CR l.val,
    Array.ofFn (n := 7800) fun k => witK k.val⟩

@[expose] noncomputable def ginvL : Array Tab := Array.ofFn (n := 5) fun j => unpack 65 7 (PL.T (CI j.val))

theorem ptsSize : (minusLEnum ()).pts.size = 7800 := by rw [pinL, Array.size_ofFn, nums.2]

theorem pt {k : ℕ} (hk : k < 7800) : (minusLEnum ()).pts[k]! = unpack 65 7 (PL.T k) :=
  ptL (by rw [nums.2]; exact hk)

theorem labC {k : ℕ} (hk : k < 7800) : clsC.lab[k]! = labK k := by
  simp only [clsC]
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem witC {k : ℕ} (hk : k < 7800) : clsC.wit[k]! = witK k := by
  simp only [clsC]
  rw [getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk), Array.getElem_ofFn]

theorem repC {l : ℕ} (hl : l < 15) : clsC.reps[l]! = CR l := by
  simp only [clsC]
  rw [getElem!_pos _ l (by rw [Array.size_ofFn]; exact hl), Array.getElem_ofFn]

theorem ginvC {j : ℕ} (hj : j < 5) : ginvL[j]! = unpack 65 7 (PL.T (CI j)) := by
  simp only [ginvL]
  rw [getElem!_pos _ j (by rw [Array.size_ofFn]; exact hj), Array.getElem_ofFn]

theorem genC {j : ℕ} (hj : j < 5) : minusLGens[j]! = unpack 65 7 (PL.G j) := bind.2 j hj

theorem sizes_size : minusLSizes.size = 15 := rfl

theorem cj_spec {k j : ℕ} (hk : k < 7800) (hj : j < 5) :
    cjK k j < 7800 ∧ PL.T (cjK k j) = pm (pm (PL.G j) (PL.T k)) (PL.T (CI j)) ∧
      labK (cjK k j) = labK k := by
  have h : cjOK k = true := by
    rcases (by omega : k < 1950 ∨ (1950 ≤ k ∧ k < 3900) ∨ (3900 ≤ k ∧ k < 5850) ∨ 5850 ≤ k)
      with h | h | h | h
    · exact AI.1 ch1383008j_0 k h
    · have e : 1950 + (k - 1950) = k := by omega
      have h' := AI.1 ch1383008j_1 (k - 1950) (by omega)
      rwa [e] at h'
    · have e : 3900 + (k - 3900) = k := by omega
      have h' := AI.1 ch1383008j_2 (k - 3900) (by omega)
      rwa [e] at h'
    · have e : 5850 + (k - 5850) = k := by omega
      have h' := AI.1 ch1383008j_3 (k - 5850) (by omega)
      rwa [e] at h'
  unfold cjOK at h
  have h2 := AI.1 h j hj
  simp only [Bool.and_eq_true] at h2
  obtain ⟨⟨h3, h4⟩, h5⟩ := h2
  exact ⟨Nat.blt_eq.mp h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5⟩

theorem wit_spec {k : ℕ} (hk : k < 7800) :
    labK k < 15 ∧ witK k < 7800 ∧
      pm (PL.T (witK k)) (PL.T (CR (labK k))) = pm (PL.T k) (PL.T (witK k)) := by
  have h := AI.1 kWit k hk
  unfold witOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem rep_spec {l : ℕ} (hl : l < 15) : CR l < 7800 ∧ labK (CR l) = l := by
  have h := AI.1 kReps l hl
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem inv_spec {j : ℕ} (hj : j < 5) :
    CI j < 7800 ∧ pm (PL.T (CI j)) (PL.G j) = pidn 65 7 := by
  have h := AI.1 kInvG j hj
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, Nat.eq_of_beq_eq_true h.2⟩

theorem szOK65 : szOK 65 7 = true := by decide

theorem cntR_eq_count (f : ℕ → Bool) (N : ℕ) :
    CFSG.KC.HeAutK.cntR f 0 N = ((List.range N).filter f).length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [CFSG.KC.HeAutK.cntR_succ, ih, Nat.zero_add, List.range_succ, List.filter_append,
      List.length_append]
    cases h : f N <;> simp [h]

theorem pmC {p q : ℕ} (hp : canonK 65 7 (mask 7) (65 * 7) p = true)
    (hq : canonK 65 7 (mask 7) (65 * 7) q = true) :
    comp 65 (unpack 65 7 p) (unpack 65 7 q) = unpack 65 7 (pm p q) :=
  CFSG.KC.BfsPin.compA_unpack hp hq

theorem idTabP : idTab 65 = unpack 65 7 (pidn 65 7) := CFSG.KC.BfsPin.idA_eq szOK65

theorem canPm {p q : ℕ} (hp : canonK 65 7 (mask 7) (65 * 7) p = true)
    (hq : canonK 65 7 (mask 7) (65 * 7) q = true) :
    canonK 65 7 (mask 7) (65 * 7) (pm p q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem enumL : Enumerates (Subgroup.closure (permsA 65 minusLGens)) (minusLEnum ()).pts.toList := by
  have h := enum_ok
  simp only [minusLEnumCheck, Bool.and_eq_true] at h
  refine enumOK_enumerates keysOKm (fun i hi => ?_) h.1
  rw [ptsSize] at hi
  rw [pt hi]
  simp [unpack]

theorem classOK_rec :
    classOKGen 65 (minusLEnum ()).pts minusLGens ginvL clsC minusLSizes = true := by
  have hnd : (minusLEnum ()).pts.toList.Nodup := enumL.nodup
  have hgs : minusLGens.size = 5 := bind.1
  simp only [classOKGen, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allBelow_eq_true,
    and_assoc, ptsSize, hgs, sizes_size]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, hgs]
    refine ⟨by simp [ginvL], fun j hj => ⟨?_, ?_⟩⟩
    · rw [ginvC hj]
      simp [unpack]
    · obtain ⟨hi, he⟩ := inv_spec hj
      rw [ginvC hj, genC hj, pmC (canL hi) (canG hj), he, idTabP]
  · intro k hk
    have e := CFSG.KC.Restr.posOf_eq hnd (k := k) (by rw [ptsSize]; exact hk)
    exact e
  · intro k hk j hj
    obtain ⟨hp, hT, hl⟩ := cj_spec hk hj
    obtain ⟨hi, -⟩ := inv_spec hj
    have hc : conjTab 65 minusLGens[j]! ginvL[j]! (minusLEnum ()).pts[k]! =
        (minusLEnum ()).pts[cjK k j]! := by
      rw [conjTab, genC hj, ginvC hj, pt hk, pmC (canG hj) (canL hk),
        pmC (canPm (canG hj) (canL hk)) (canL hi), pt hp, hT]
    rw [hc, CFSG.KC.Restr.posOf_eq hnd (by rw [ptsSize]; exact hp), labC hp, labC hk, hl]
    exact ⟨(CFSG.KS.PEnum.found_indexOf_iff _ _).2 ⟨cjK k j, by rw [ptsSize]; exact hp, rfl⟩,
      rfl⟩
  · simp [clsC]
  · intro l hl
    obtain ⟨h1, h2⟩ := rep_spec hl
    rw [repC hl, labC h1]
    exact ⟨h1, h2⟩
  · intro k hk
    obtain ⟨h1, h2, h3⟩ := wit_spec hk
    obtain ⟨h4, -⟩ := rep_spec h1
    rw [labC hk, witC hk, repC h1, pt h2, pt h4, pt hk, pmC (canL h2) (canL h4),
      pmC (canL hk) (canL h2), h3]
    exact ⟨by simp [h1], by simp [h2], rfl⟩
  · intro l hl
    have hcnt := Nat.eq_of_beq_eq_true (AI.1 kCount l hl)
    have e : (List.range 7800).filter (fun k => clsC.lab[k]! == l) =
        (List.range 7800).filter (fun k => Nat.beq (labK k) l) :=
      List.filter_congr fun k hk => by
        rw [labC (List.mem_range.1 hk)]
        cases h : Nat.beq (labK k) l
        · rw [beq_eq_false_iff_ne]
          exact Nat.ne_of_beq_eq_false h
        · rw [beq_iff_eq]
          exact Nat.eq_of_beq_eq_true h
    exact (congrArg List.length e).trans ((cntR_eq_count _ _).symm.trans hcnt)
  · omega
  · have h := kIdL
    simp only [Bool.and_eq_true] at h
    rw [pt (by omega), Nat.eq_of_beq_eq_true h.1, idTabP]
  · have h := kIdL
    simp only [Bool.and_eq_true] at h
    rw [labC (by omega), Nat.eq_of_beq_eq_true h.2]

theorem class_ok : ∃ e : Fin minusLSizes.size ≃ ConjClasses minusLPerm,
    (∀ l, Nat.card (e l).carrier = minusLSizes[l.val]!) ∧
      ∃ l₀ : Fin minusLSizes.size, l₀.val = 0 ∧ e l₀ = ConjClasses.mk 1 := by
  have hA : ∀ a ∈ permsA 65 minusLGens, ∃ j < minusLGens.size, TabRep minusLGens[j]! a := by
    rintro a ⟨j, hj, rfl⟩
    have hj5 : j < 5 := by rwa [bind.1] at hj
    have hv : validA 65 minusLGens[j]! = true := by
      have h := gens_ok
      simp only [minusLGensCheck, Bool.and_eq_true] at h
      exact allLt_spec h.1.1.1.1.1.2 (i := j) hj5
    refine ⟨j, hj, ?_, rep_of_validA hv⟩
    rw [genC hj5]
    simp [unpack]
  exact classes_of_classOKGen hA enumL classOK_rec

end CertificateChecks.KernelMinusL
