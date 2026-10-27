
module

public import Certificates.Kernel.SporSch.HN.Invol2099T
public import Certificates.Kernel.SporSch.HN.Strong
public import CFSG.Certificates.Kernel.SporSch.HNF5RankSound
public import CFSG.Certificates.Kernel.SporSch.HNF5InvSound
public import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.HNF5KronTSound
import CFSG.Certificates.Kernel.PackSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNInvol

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNSchreier CFSG.ONSchreier.Native CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HNStrong CertificateChecks.KernelSporSch.HNInvolU

theorem entK {K : Nat} (hK : K < 62) : Canon5 (sx K) ∧
    (HNI.OP K = 0 → Canon5 (sx (HNI.L K)) → Canon5 (sx (HNI.R K)) →
      ∀ i < 133, vm5 (sx (HNI.R K)) (sx (HNI.L K) i) = sx K i) ∧
    (HNI.OP K = 1 → ∀ i < 133, sx (HNI.L K) i = sx K i) ∧
    (HNI.OP K = 3 → Canon5 (sx (HNI.L K)) → ∀ i < 133, trRow5 (sx (HNI.L K)) i = sx K i) := by
  rcases (by omega : K < 11 ∨ (11 ≤ K ∧ K < 21) ∨ (21 ≤ K ∧ K < 31) ∨ (31 ≤ K ∧ K < 41) ∨
      (41 ≤ K ∧ K < 51) ∨ 51 ≤ K) with h | h | h | h | h | h
  · exact F5Kron.krBlkT_sound blk0 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound blk1 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound blk2 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound blk3 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound blk4 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound blk5 (by omega) (by omega)

theorem entKU {K : Nat} (hK : K < 62) : Canon5 (su K) ∧
    (HNIU.OP K = 0 → Canon5 (su (HNIU.L K)) → Canon5 (su (HNIU.R K)) →
      ∀ i < 133, vm5 (su (HNIU.R K)) (su (HNIU.L K) i) = su K i) ∧
    (HNIU.OP K = 1 → ∀ i < 133, su (HNIU.L K) i = su K i) ∧
    (HNIU.OP K = 3 → Canon5 (su (HNIU.L K)) →
      ∀ i < 133, trRow5 (su (HNIU.L K)) i = su K i) := by
  rcases (by omega : K < 11 ∨ (11 ≤ K ∧ K < 21) ∨ (21 ≤ K ∧ K < 31) ∨ (31 ≤ K ∧ K < 41) ∨
      (41 ≤ K ∧ K < 51) ∨ 51 ≤ K) with h | h | h | h | h | h
  · exact F5Kron.krBlkT_sound HNInvolU.blk0 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound HNInvolU.blk1 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound HNInvolU.blk2 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound HNInvolU.blk3 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound HNInvolU.blk4 (by omega) (by omega)
  · exact F5Kron.krBlkT_sound HNInvolU.blk5 (by omega) (by omega)

theorem canon (k : Nat) (hk : k < 62) : Canon5 (sx k) := (entK hk).1

theorem canonU (k : Nat) (hk : k < 62) : Canon5 (su k) := (entKU hk).1

theorem specL {K : Nat} (hK : K < 62) : HNI.L K < 62 ∧ HNI.R K < 62 := by
  have hs := CFSG.KC.Pack.allN_spec specLt K hK
  rw [CFSG.KC.Pack.band_iff, Nat.blt_eq, Nat.blt_eq] at hs
  exact hs

theorem specLU {K : Nat} (hK : K < 62) : HNIU.L K < 62 ∧ HNIU.R K < 62 := by
  have hs := CFSG.KC.Pack.allN_spec HNInvolU.specLt K hK
  rw [CFSG.KC.Pack.band_iff, Nat.blt_eq, Nat.blt_eq] at hs
  exact hs

theorem canonX (i : Nat) (hi : i < 462) : canon5 (sx 58 i) = true := by
  have e : sx 58 i = sx (58 + i / 133) (i % 133) := by
    unfold sx slice5
    congr 1
    rw [Nat.add_eq, Nat.mul_eq, Nat.add_eq, Nat.mul_eq, Nat.add_mul, Nat.add_assoc,
      Nat.div_add_mod']
  rw [e]
  exact canon _ (by omega) _ (Nat.mod_lt _ (by omega))

theorem mulE {K l r : Nat} (hK : K < 62) (ho : HNI.OP K = 0) (hl : HNI.L K = l)
    (hr : HNI.R K = r) : ∀ i < 133, vm5 (sx r) (sx l i) = sx K i := by
  subst hl hr
  exact (entK hK).2.1 ho (canon _ (specL hK).1) (canon _ (specL hK).2)

theorem mul_eq {K l r : Nat} (hl1 : l < 62) (hr1 : r < 62) (hK : K < 62) (ho : HNI.OP K = 0)
    (hl : HNI.L K = l) (hr : HNI.R K = r) :
    mulM 5 133 (rows5 (sx l)) (rows5 (sx r)) = rows5 (sx K) :=
  mulM5_sound (canon l hl1) (canon r hr1) (mulE hK ho hl hr)

theorem copyE {K l : Nat} (hK : K < 62) (ho : HNI.OP K = 1) (hl : HNI.L K = l) :
    ∀ i < 133, sx l i = sx K i := by
  subst hl
  exact (entK hK).2.2.1 ho

theorem mulEU {K l r : Nat} (hK : K < 62) (ho : HNIU.OP K = 0) (hl : HNIU.L K = l)
    (hr : HNIU.R K = r) : ∀ i < 133, vm5 (su r) (su l i) = su K i := by
  subst hl hr
  exact (entKU hK).2.1 ho (canonU _ (specLU hK).1) (canonU _ (specLU hK).2)

theorem copyEU {K l : Nat} (hK : K < 62) (ho : HNIU.OP K = 1) (hl : HNIU.L K = l) :
    ∀ i < 133, su l i = su K i := by
  subst hl
  exact (entKU hK).2.2.1 ho

theorem cols_eq {K l : Nat} (hK : K < 62) (ho : HNI.OP K = 3) (hl : HNI.L K = l) :
    colsMat 133 (rows5 (sx K)) = rows5 (sx l) :=
  (trans5_sound (T := sx l) (Tt := sx K) (by
    subst hl
    exact (entK hK).2.2.2 ho (canon _ (specL hK).1))).2

theorem rows_eq {X T : Nat → Nat} (h : allN 133 (fun i => Nat.beq (X i) (T i)) = true) :
    rows5 X = rows5 T :=
  rows5_congr fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem isId {X : Nat → Nat} (h : allN 133 (fun i => Nat.beq (X i) (idRow5 i)) = true) :
    (rows5 X == idM 133) = true :=
  eqId5_sound fun i hi => Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem rowsA_eq : rowsA = rows5 (sx 0) := by
  rw [HNStrong.rowsA_eq, rows_eq eqA]

theorem rowsB_eq : rowsB = rows5 (sx 1) := by
  rw [HNStrong.rowsB_eq, rows_eq eqB]

theorem F_eq {j : Nat} (hj : j < 17) : F j = rows5 (sx (4 + j)) := by
  have := allN_spec eqH j hj
  rw [F]
  refine rows5_congr fun i hi => ?_
  have e := Nat.eq_of_beq_eq_true (allN_spec this i hi)
  rw [Nat.add_eq, Nat.add_eq] at e
  exact e.symm

theorem strongOK : strongOKM (progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)[1]!
    (progRegsM (initRegsM rowsA rowsB) Data.subgroupProgram)[2]! SA SIA LocalData.strongWords =
      true := by
  have hsz := strong_parts.1
  have gS : ∀ j < 17, SA[j]! = F j := fun j hj => ofFn_getElem! hj
  have gSi : ∀ j < 17, SIA[j]! = FI j := fun j hj => ofFn_getElem! (F := FI) hj
  have e1 : SA.size = 17 := by simp [SA]
  have e2 : SIA.size = 17 := by simp [SIA]
  unfold strongOKM
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [hsz]
    rfl
  · rw [e1, hsz]
    rfl
  · rw [e2, hsz]
    rfl
  · rw [gS 0 (by omega), regs_12.1]
    exact beq_self_eq_true _
  · rw [gS 1 (by omega), regs_12.2]
    exact beq_self_eq_true _
  · rw [e1]
    refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rw [gS j hj, gSi j hj]
    exact F_mul_FI hj
  · rw [e1]
    refine CFSG.ONSchreier.allBelowN_iff.2 fun j hj => ?_
    rcases Nat.lt_or_ge j 2 with h | h
    · simp [h]
    · obtain ⟨hl, hw⟩ := words_ok h hj
      have hp : plettersOK j LocalData.strongWords[j]! = true := by
        simp only [plettersOK, List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
          decide_eq_true_eq]
        exact hl
      rw [gS j hj, hw, hp]
      simp

@[expose] def ltD (l : Int) : Nat := 3 + l.toNat

theorem mletter_D {l : Int} (h0 : 0 < l) (h17 : l.natAbs ≤ 17) :
    mletter SA SIA l = rows5 (sx (ltD l)) := by
  rw [mletter, if_pos h0, SA, ofFn_getElem! (by omega), F_eq (by omega), ltD]
  congr 2
  omega

theorem chD : chainOK HNI.OP HNI.L HNI.R ltD 62 LocalData.innerWord 23 = true := by quickRfl

theorem inner_pos : ∀ l ∈ LocalData.innerWord, 0 < l ∧ l.natAbs ≤ 17 := by decide

theorem D_eq : mword SA SIA LocalData.innerWord = rows5 (sx 33) :=
  F5Kron.chainK_eq (fun _ hk ho => mulE hk ho rfl rfl) (fun _ hk ho => copyE hk ho rfl) canon
    (fun l hl => mletter_D (inner_pos l hl).1 (inner_pos l hl).2) chD

@[expose] noncomputable def ltc (l : Nat) : Nat := nIf(Nat.beq l 1, 0, 1)

theorem outer_mem : ∀ l ∈ LocalData.outerWord, l = 1 ∨ l = 2 := by decide

theorem root_mem : ∀ l ∈ LocalData.rootWord, l = 1 ∨ l = 2 := by decide

theorem sel_rowsU {l : Nat} (hl : l = 1 ∨ l = 2) :
    seedSel (rows5 (su 0)) (rows5 (su 1)) l = rows5 (su (ltc l)) := by
  rcases hl with rfl | rfl
  · rw [seedSel, if_pos rfl]
    rfl
  · rw [seedSel, if_neg (by decide), if_pos rfl]
    rfl

theorem sel_cols {l : Nat} (hl : l = 1 ∨ l = 2) :
    seedSel (rows5 (sx 0)) (rows5 (sx 1)) l = colsMat 133 (rows5 (sx (ltT l))) := by
  rcases hl with rfl | rfl
  · rw [seedSel, if_pos rfl]
    exact (cols_eq (K := 2) (l := 0) (by omega) rfl rfl).symm
  · rw [seedSel, if_neg (by decide), if_pos rfl]
    exact (cols_eq (K := 3) (l := 1) (by omega) rfl rfl).symm

@[expose] noncomputable def chainUB : Bool :=
  (List.range 57).all fun u => HNIU.OP (3 + u) == 0 && HNIU.L (3 + u) == 2 + u &&
    HNIU.R (3 + u) == ltc (LocalData.outerWord.getD (u + 1) 0)

theorem chU : chainUB = true := by quickRfl

theorem outer_len : LocalData.outerWord.length = 58 := by decide

theorem U_eq : wordM (seedSel rowsA rowsB) LocalData.outerWord = rows5 (su 59) := by
  have hc := chU
  simp only [chainUB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hc
  have hl : ∀ l ∈ LocalData.outerWord, ltc l < 62 := fun l h => by
    rcases outer_mem l h with rfl | rfl <;> decide
  rw [HNSeeds.rowsA_eq, HNSeeds.rowsB_eq, ← rows_eq HNInvolU.eqA, ← rows_eq HNInvolU.eqB]
  have := wordM5_chain (Ms := seedSel (rows5 (su 0)) (rows5 (su 1))) (LT := fun l => su (ltc l))
    (Q := fun t => su (1 + t)) (w := LocalData.outerWord) (by rw [outer_len]; omega)
    (fun l h => sel_rowsU (outer_mem l h)) (fun l h => canonU _ (hl l h))
    (fun t _ ht => canonU _ (by rw [outer_len] at ht; omega))
    (fun i hi => (copyEU (K := 2) (l := ltc (LocalData.outerWord.headD 0)) (by omega) rfl rfl i
      hi).symm) (fun t h1 ht i hi => ?_)
  · rwa [outer_len] at this
  · rw [outer_len] at ht
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    obtain ⟨⟨a, b⟩, c⟩ := hc u (by omega)
    have := mulEU (by omega) a b c i hi
    rw [show 2 + u = 1 + (u + 1) by omega, show 3 + u = 1 + (u + 1 + 1) by omega] at this
    exact this

theorem Ui_eq : invM 5 133 (rows5 (su 59)) = rows5 (sx 34) := by
  rw [rows_eq eqUi]
  exact invM5_eq (canonU 59 (by omega)) (canonU 60 (by omega)) fun i hi => by
    rw [mulEU (K := 61) (l := 59) (r := 60) (by omega) rfl rfl rfl i hi]
    exact Nat.eq_of_beq_eq_true (allN_spec id61 i hi)

@[expose] noncomputable def chainWB : Bool :=
  (List.range 7).all fun u => HNI.OP (46 + u) == 0 && HNI.L (46 + u) == 45 + u &&
    HNI.R (46 + u) == 44

theorem chW : chainWB = true := by quickRfl

theorem W_eq : powM 5 133 (mulM 5 133 (rows5 (sx 0)) (mulM 5 133 (rows5 (sx 1)) (rows5 (sx 1)))) 8 =
    rows5 (sx 52) := by
  have hc := chW
  simp only [chainWB, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at hc
  rw [mul_eq (K := 43) (l := 1) (r := 1) (by omega) (by omega) (by omega) rfl rfl rfl,
    mul_eq (K := 44) (l := 0) (r := 43) (by omega) (by omega) (by omega) rfl rfl rfl]
  refine powM5_chain (M := sx 44) (P := fun t => sx (44 + t)) (by omega) (canon _ (by omega))
    (fun t _ ht => canon _ (by omega)) (fun i hi => (copyE (K := 45) (l := 44) (by omega) rfl rfl i hi).symm)
    (fun t h1 ht i hi => ?_)
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  obtain ⟨⟨a, b⟩, c⟩ := hc u (by omega)
  have := mulE (by omega) a b c i hi
  rw [show 45 + u = 44 + (u + 1) by omega, show 46 + u = 44 + (u + 1 + 1) by omega] at this
  exact this

theorem rootVec_eq : rootVec = vec5 (sx 57 0) := by
  rw [rootVec, HNRoot.eq]
  exact root5_sound root

theorem root_len : LocalData.rootWord.length = 40 := by decide

theorem x0_eq : seedWordVec (rows5 (sx 0)) (rows5 (sx 1)) LocalData.rootWord (vec5 (sx 57 0)) =
    vec5 (sx 57 40) := by
  have hr := allN_spec rchain
  have key : ∀ k ≤ 40, (LocalData.rootWord.drop (40 - k)).foldr
      (fun l y => mulVec 5 133 (seedSel (rows5 (sx 0)) (rows5 (sx 1)) l) y) (vec5 (sx 57 0)) =
        vec5 (sx 57 k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Nat.sub_zero, List.drop_of_length_le (by rw [root_len]), List.foldr_nil]
    | succ k ih =>
      intro hk
      have hlt : 40 - (k + 1) < LocalData.rootWord.length := by rw [root_len]; omega
      have e : LocalData.rootWord.drop (40 - (k + 1)) =
          LocalData.rootWord.getD (39 - k) 0 :: LocalData.rootWord.drop (40 - k) := by
        rw [List.drop_eq_getElem_cons hlt, List.getD_eq_getElem _ _ (by rw [root_len]; omega)]
        congr 2 <;> omega
      have hm : LocalData.rootWord.getD (39 - k) 0 ∈ LocalData.rootWord := by
        rw [List.getD_eq_getElem _ _ (by rw [root_len]; omega)]
        exact List.getElem_mem _
      have hmem := root_mem _ hm
      have hlt2 : ltT (LocalData.rootWord.getD (39 - k) 0) < 62 := by
        rcases hmem with h | h <;> rw [h] <;> decide
      rw [e, List.foldr_cons, ih (by omega), sel_cols hmem,
        mulVec5_sound (canon _ hlt2) (canon 57 (by omega) k (by omega))]
      have := hr k (by rw [root_len]; omega)
      rw [root_len] at this
      have e2 : Nat.sub (Nat.sub 40 1) k = 39 - k := rfl
      rw [e2] at this
      have e3 : sx 57 (k + 1) = vm5 (sx (ltT (LocalData.rootWord.getD (39 - k) 0))) (sx 57 k) :=
        Nat.eq_of_beq_eq_true this
      rw [e3]
  have := key 40 (le_refl _)
  rwa [Nat.sub_self, List.drop_zero] at this

theorem xrec (i : Nat) (h1 : 1 ≤ i) (hi : i < 462) :
    (LocalData.parents.getD i (0, 0)).1 < i ∧
      ((LocalData.parents.getD i (0, 0)).2 = 1 ∨ (LocalData.parents.getD i (0, 0)).2 = 2) ∧
      vm5 (slice5 HNI.MT (nIf(Nat.beq (LocalData.parents.getD i (0, 0)).2 1, 21, 22)))
        (slice5 HNI.MT 58 (LocalData.parents.getD i (0, 0)).1) = slice5 HNI.MT 58 i := by
  have h : recRow5 HNI.MT 58 21 22 LocalData.parents i = true := by
    rcases Nat.lt_or_ge i 231 with a | a
    · have := allBlk_spec xrec0 (i - 1) (by omega)
      rwa [show Nat.add 1 (i - 1) = i by rw [Nat.add_eq]; omega] at this
    · have := allBlk_spec xrec1 (i - 231) (by omega)
      rwa [show Nat.add 231 (i - 231) = i by rw [Nat.add_eq]; omega] at this
  unfold recRow5 at h
  rw [CFSG.KS.Raw.strictB_eq, CFSG.KS.Raw.strictB_eq] at h
  obtain ⟨a, bc⟩ := (bAnd_iff _ _).1 h
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 bc
  refine ⟨Nat.le_of_ble_eq_true a, ?_, Nat.eq_of_beq_eq_true c⟩
  cases h1' : Nat.beq (LocalData.parents.getD i (0, 0)).2 1
  · rw [h1'] at b
    exact Or.inr (Nat.eq_of_beq_eq_true b)
  · exact Or.inl (Nat.eq_of_beq_eq_true h1')

theorem parents_len : LocalData.parents.length = 462 := by decide

theorem H0_eq : SA[0]! = colsMat 133 (rows5 (slice5 HNI.MT 21)) := by
  rw [SA, ofFn_getElem! (by omega), F_eq (by omega)]
  exact (cols_eq (K := 21) (l := 4) (by omega) rfl rfl).symm

theorem H1_eq : SA[1]! = colsMat 133 (rows5 (slice5 HNI.MT 22)) := by
  rw [SA, ofFn_getElem! (by omega), F_eq (by omega)]
  exact (cols_eq (K := 22) (l := 5) (by omega) rfl rfl).symm

theorem x0_row : vec5 (slice5 HNI.MT 58 0) = vec5 (sx 57 40) := by
  change vec5 (sx 58 0) = _
  rw [Nat.eq_of_beq_eq_true x0]

theorem lab_size : labMasks.size = 462 := by simp [labMasks]; rfl

theorem lab_get {j : Nat} (hj : j < 462) : labMasks[j]! = HNLab j := by
  have h := Nat.eq_of_beq_eq_true (allN_spec labEq j hj)
  have hs : j < LocalData.labels.size := by
    have := lab_size
    simp only [labMasks, Array.size_map] at this
    omega
  rw [h, labMasks, getElem!_pos _ j (by simpa using hs), Array.getElem_map,
    getElem!_pos LocalData.labels j hs]

theorem tau_parts {i : Nat} (hi : i < 462) : HNTau i < 462 ∧ HNLab (HNTau i) = tgt i ∧
    ∀ j < HNTau i, HNLab j ≠ tgt i := by
  have h := allN_spec tauOK i hi
  rw [CFSG.KS.Raw.strictB_eq] at h
  obtain ⟨a, bc⟩ := (bAnd_iff _ _).1 h
  obtain ⟨b, c⟩ := (bAnd_iff _ _).1 bc
  refine ⟨by simpa [Nat.blt_eq] using a, Nat.eq_of_beq_eq_true b, fun j hj he => ?_⟩
  have := allN_spec c j hj
  rw [he, Nat.beq_refl] at this
  exact absurd this (by decide)

theorem tau_get {i : Nat} (hi : i < 462) : tauIdx[i]! = HNTau i := by
  obtain ⟨ht, hb, hc⟩ := tau_parts hi
  have hf : labMasks.findIdx? (· == canonMask (permMask tauArr labMasks[i]!)) = some (HNTau i) := by
    rw [Array.findIdx?_eq_some_iff_getElem]
    refine ⟨by rw [lab_size]; exact ht, ?_, fun j hji => ?_⟩
    · rw [← getElem!_pos labMasks _ (by rw [lab_size]; exact ht), lab_get ht, lab_get hi, hb]
      exact beq_self_eq_true _
    · rw [← getElem!_pos labMasks j (by rw [lab_size]; omega), lab_get (by omega), lab_get hi]
      simpa [tgt] using hc j hji
  rw [tauIdx, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hf]
  rfl

theorem bnot {b : Bool} (h : Bool.not b = true) : b = false := by
  cases b <;> simp_all

theorem facts : involChecks rowsA rowsB (rowsOf 5 133 LocalData.normalizerPayload)
    (rowsOf 5 133 LocalData.involutionPayload) tauIdx labMasks = true := by
  obtain ⟨xsz, xget, xall⟩ := xvec5_sound (MT := HNI.MT) (kA := 21) (kB := 22) (kV := 58)
    (H := SA) (x0 := vec5 (sx 57 40)) (recs := LocalData.parents) H0_eq H1_eq
    (canon 21 (by omega)) (canon 22 (by omega)) canonX parents_len x0_row xrec
  have hS : rowsOf 5 133 LocalData.normalizerPayload = rows5 (sx 35) := by
    rw [HNNorm.eq]
    exact pay5_sound payS
  have hC : rowsOf 5 133 LocalData.involutionPayload = rows5 (sx 36) := by
    rw [HNInv.eq]
    exact pay5_sound payC
  have hCt : rows5 (sx 36) = colsMat 133 (rows5 (sx 40)) :=
    (cols_eq (K := 40) (l := 36) (by omega) rfl rfl).symm
  unfold involChecks
  dsimp only
  rw [strong_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, strongOK⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [regs_ok.1]
    rfl
  · rw [U_eq, Ui_eq, rows_eq eqUi, mulM5_sound (canonU 59 (by omega)) (canonU 60 (by omega))
      (mulEU (K := 61) (l := 59) (r := 60) (by omega) rfl rfl rfl)]
    exact isId id61
  · rw [U_eq, Ui_eq, D_eq, hS, hC,
      mul_eq (K := 37) (l := 33) (r := 34) (by omega) (by omega) (by omega) rfl rfl rfl,
      mul_eq (K := 38) (l := 37) (r := 35) (by omega) (by omega) (by omega) rfl rfl rfl, rows_eq e38]
    exact beq_self_eq_true _
  · rw [hC, mul_eq (K := 39) (l := 36) (r := 36) (by omega) (by omega) (by omega) rfl rfl rfl]
    exact isId id39
  · rw [hC]
    obtain ⟨i, hi, hn⟩ := anyN_spec ne36
    refine notId5_sound (canon 36 (by omega)) ⟨i, hi, fun he => ?_⟩
    have := bnot hn
    rw [he, Nat.beq_refl] at this
    exact absurd this (by decide)
  · rw [hC, hCt, rootVec_eq, mulVec5_sound (canon 40 (by omega)) (canon 57 (by omega) 0 (by omega)),
      Nat.eq_of_beq_eq_true fixv]
    exact beq_self_eq_true _
  · rw [hS, rowsA_eq,
      mul_eq (K := 41) (l := 35) (r := 0) (by omega) (by omega) (by omega) rfl rfl rfl,
      mul_eq (K := 42) (l := 0) (r := 35) (by omega) (by omega) (by omega) rfl rfl rfl, rows_eq e41]
    exact beq_self_eq_true _
  · rw [hS, rowsA_eq, rowsB_eq, W_eq,
      mul_eq (K := 53) (l := 35) (r := 1) (by omega) (by omega) (by omega) rfl rfl rfl,
      mul_eq (K := 54) (l := 52) (r := 53) (by omega) (by omega) (by omega) rfl rfl rfl,
      mul_eq (K := 55) (l := 52) (r := 35) (by omega) (by omega) (by omega) rfl rfl rfl,
      mul_eq (K := 56) (l := 1) (r := 55) (by omega) (by omega) (by omega) rfl rfl rfl, rows_eq e54]
    exact beq_self_eq_true _
  · rw [rowsA_eq, rowsB_eq, rootVec_eq, x0_eq, xsz]
    rfl
  · rw [rowsA_eq, rowsB_eq, rootVec_eq, x0_eq, xget 0 (by omega)]
    exact beq_self_eq_true _
  · rw [rowsA_eq, rowsB_eq, rootVec_eq, x0_eq]
    exact xall
  · rw [tauIdx, Array.size_ofFn]
    rfl
  · rw [hC, hCt, rowsA_eq, rowsB_eq, rootVec_eq, x0_eq]
    refine CFSG.ONSchreier.allBelowN_iff.2 fun i hi => ?_
    obtain ⟨ht, hb, -⟩ := tau_parts hi
    have hcx : vm5 (sx 40) (sx 58 i) = sx 58 (HNTau i) := by
      rcases Nat.lt_or_ge i 231 with p | p
      · have := allBlk_spec cx0 i p
        rw [show Nat.add 0 i = i by rw [Nat.add_eq]; omega] at this
        exact Nat.eq_of_beq_eq_true this
      · have := allBlk_spec cx1 (i - 231) (by omega)
        rw [show Nat.add 231 (i - 231) = i by rw [Nat.add_eq]; omega] at this
        exact Nat.eq_of_beq_eq_true this
    rw [tau_get hi, lab_get ht, lab_get hi, xget i hi, xget _ ht]
    change (decide (HNTau i < 462) && HNLab (HNTau i) == canonMask (permMask tauArr (HNLab i)) &&
      mulVec 5 133 (colsMat 133 (rows5 (sx 40))) (vec5 (sx 58 i)) == vec5 (sx 58 (HNTau i))) = true
    rw [mulVec5_sound (canon 40 (by omega)) (canonX i hi), hcx, hb]
    simp [ht, tgt]

end CertificateChecks.KernelSporSch.HNInvol

end
