
module

public import Certificates.Kernel.Tc.RuFacts
public import Certificates.Kernel.Tc.RuSift2
public import Certificates.Kernel.Tc.RuThreeK
public import Certificates.Kernel.Tc.RuThreeTail
public import CFSG.Certificates.Kernel.HeLoc.PTailSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc
open CFSG.KC.TcF CFSG.KC.B3S3K CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.HexFlat
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier CFSG.Certificates.Native
open CFSG.AGLEmbeddingD2.Wilson CFSG.AGLEmbeddingD2.Wilson.ThetaSpor
open CertificateChecks.KernelSporSch

theorem ok3' {k : Nat} (hk : k < 31) :
    permOK 4060 12 (mask 12) (4060 * 12) (R3.F k) (I3 k) = true ∧
      allN 4060 (fun i => Nat.blt (pg 12 (mask 12) (R3.F k) i) 4060) = true := by
  rcases Nat.lt_or_ge k 3 with h | h
  · exact ok3_k h
  · have h1 := Orb.allN_iff.1 kOk3b (k - 3) (by omega)
    have e : Nat.add 3 (k - 3) = k := by
      simp only [Nat.add_eq]
      omega
    rw [e] at h1
    unfold ok3 at h1
    exact (bAnd_iff _ _).1 h1

theorem siftJ3 {k : Nat} (hk : k < 31) : siftJ (R3.F k) = true := by
  rcases Nat.lt_or_ge k 3 with h | h
  · exact Orb.allN_iff.1 kSift3 k h
  · have h1 := Orb.allN_iff.1 kSift3b (k - 3) (by omega)
    have e : Nat.add 3 (k - 3) = k := by
      simp only [Nat.add_eq]
      omega
    rwa [e] at h1

theorem inv3' {k : Nat} (hk : k < 31) :
    invCand 4060 (unpack 4060 12 (R3.F k)) = unpack 4060 12 (I3 k) ∧
      isInvA 4060 (unpack 4060 12 (R3.F k)) (unpack 4060 12 (I3 k)) = true :=
  invEqK_sound (ok3' hk).1

theorem valid3' {k : Nat} (hk : k < 31) : validA 4060 (unpack 4060 12 (R3.F k)) = true := by
  unfold validA
  rw [(inv3' hk).1]
  exact (inv3' hk).2

theorem rep3' {k : Nat} (hk : k < 31) : Rep 4060 (unpack 4060 12 (R3.F k)) (gp3 k) :=
  (rep_permOfArr (inv3' hk).2).1

theorem repF3' {k : Nat} (hk : k < 31) : RepF 4060 (t3 k) (gp3 k) := repF_of_rep (rep3' hk)

theorem repF3i' {k : Nat} (hk : k < 31) : RepF 4060 (i3 k) (gp3 k)⁻¹ :=
  repF_of_rep (rep_permOfArr (inv3' hk).2).2

theorem sift3' {k : Nat} (hk : k < 31) :
    siftA 4060 (rawLevels 4060 (ruField4060 3) (ruBaseArr 4060 ruJoinBase))
      (ruBaseArr 4060 ruJoinBase) 0 (unpack 4060 12 (R3.F k)) = true :=
  siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl rfl (hi_of_permOK (ok3' hk).1) (ok3' hk).2
    (siftJ3 hk)

theorem arrE {k : Nat} (hk : k < 31) : ruArr3 k = unpack 4060 12 (R3.F k) := arr3 hk

theorem exists_of_anyF {N : Nat} {f : Nat → Bool} (h : anyF N f = true) : ∃ j < N, f j = true := by
  unfold anyF at h
  cases hall : allN N fun j => bIf(f j, false, true)
  · by_contra hne
    have : allN N (fun j => bIf(f j, false, true)) = true :=
      Orb.allN_iff.2 fun j hj => by
        have e : f j = false := by
          cases e' : f j
          · rfl
          · exact absurd ⟨j, hj, e'⟩ hne
        rw [e]
    rw [hall] at this
    exact Bool.false_ne_true this
  · rw [hall] at h
    exact absurd h Bool.false_ne_true

theorem beq_eq_nbeq (a b : Nat) : (a == b) = Nat.beq a b := by
  cases h : Nat.beq a b
  · have : a ≠ b := fun e => by rw [e, Nat.beq_refl] at h; exact Bool.false_ne_true h.symm
    simpa using this
  · simpa using Nat.eq_of_beq_eq_true h

theorem sk_lt {SK SKI : Nat → Nat} {N : Nat}
    (h : ∀ j < N, SKI j < N ∧ SK (SKI j) = j) : ∀ j < N, SK j < N := by
  have hinj : Set.InjOn SKI (Finset.range N : Set Nat) := fun a ha b hb e => by
    rw [← (h a (by simpa using ha)).2, ← (h b (by simpa using hb)).2, e]
  have himg : (Finset.range N).image SKI = Finset.range N := Finset.eq_of_subset_of_card_le
    (fun y hy => by
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_range.2 (h a (by simpa using ha)).1)
    (by rw [Finset.card_image_of_injOn hinj])
  intro j hj
  have : j ∈ (Finset.range N).image SKI := by rw [himg]; simpa using hj
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 this
  rw [(h a (by simpa using ha)).2]
  simpa using ha

theorem csk_lt : ∀ j < 2160, TC.SK j < 2160 := sk_lt fun j hj => by
  have h := Orb.allN_iff.1 kSortC j hj
  unfold sortAtK at h
  rw [bAnd_iff, bAnd_iff, Nat.blt_eq] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1⟩

section Ru

theorem mem3' {k : Nat} (hk : k < 31) : gp3 k ∈ ruP := mem_ruP_of_sift (rep3' hk) (sift3' hk)

theorem eqA_P {a b : Array Nat} {A B : Equiv.Perm (Fin 4060)} {f g : Nat → Nat}
    (ha : Rep 4060 a A) (hb : Rep 4060 b B) (hf : RepF 4060 f A) (hg : RepF 4060 g B)
    (hA : A ∈ ruP) (hB : B ∈ ruP) (h : eqOnL bs f g = true) : eqA 4060 a b = true :=
  (eqA_iff ha hb).2 (eq_of_eqOnL faithful hf hg hA hB h)

theorem key_faith {a b : Array Nat} {A B : Equiv.Perm (Fin 4060)} (ha : Rep 4060 a A)
    (hb : Rep 4060 b B) (hA : A ∈ ruP) (hB : B ∈ ruP)
    (h : keyA 4060 ruKeys a = keyA 4060 ruKeys b) : A = B := by
  have hl := Nat.ofDigits_inj_of_len_eq (b := 4060) (by norm_num) (by simp)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [ha.apply (keys_lt p hp)]
      exact (A _).2)
    (fun l hl => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hl
      rw [hb.apply (keys_lt p hp)]
      exact (B _).2) h
  have hpt : ∀ c (hc : c ∈ bs), (A ⟨c, bs_lt c hc⟩ : Nat) = B ⟨c, bs_lt c hc⟩ := by
    intro c hc
    have hc' : c ∈ ruKeys := hc
    have := List.map_inj_left.1 hl c hc'
    rwa [ha.apply (keys_lt c hc'), hb.apply (keys_lt c hc')] at this
  exact hF2 A hA B hB (iff_of_true hA hB) hpt

theorem strong_mem {j : Nat} (hj : j < 18) : permOfArr 4060 (ruField4060 3)[j]! ∈ ruP := by
  have hb := RuJ.bindsO.2.2.2.2.1 j hj
  have hp := Orb.allN_iff.1 RuJ.permO j hj
  have hinv := invEqK_sound hp
  have hrep : Rep 4060 (unpack 4060 12 (RuJO.S j)) (permOfArr 4060 (unpack 4060 12 (RuJO.S j))) :=
    (rep_permOfArr hinv.2).1
  have hs := siftK_soundR RuJ.bindsJ RuJ.permJ RuJS.hl rfl (hi_of_permOK hp)
    (Orb.allN_iff.1 kRangeS j hj) (Orb.allN_iff.1 kSiftS j hj)
  rw [hb]
  exact mem_ruP_of_sift hrep hs

theorem gen_le : Subgroup.closure (Set.range fun j : Fin 18 =>
    permOfArr 4060 (ruField4060 3)[j.val]!) ≤ ruP := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact strong_mem j.2

theorem tabsJ : TabsT 4060 12 18 4 RuJO.BP RuJT.NR RuJT.NR RuJO.S RuJO.SI RuJO.LR RuJT.Ts RuJT.LT
    RuJT.PT RuJT.QT 143 1024 4 1024 :=
  ⟨by decide, by decide, by decide, by decide, RuJ.TS.all, RuJ.LT.all, RuJ.ptB_all, RuJ.qtB_all⟩

theorem tcJ : TabChain 4060 12 18 4 RuJO.BP 254 16 RuJT.NR RuJT.NR 143 1024 4 1024 RuJO.S RuJO.SI
    RuJO.LR RuJT.Ts RuJT.LT RuJT.PT RuJT.QT (ruField4060 3) (ruBaseArr 4060 ruJoinBase) bs :=
  ⟨RuJ.bindsO, RuJ.permO, RuJO.ho, by norm_num, tabsJ, rfl⟩

theorem fr_ok : ∀ i < 4, fr i = 0 ∨ ∃ l e, fr i = 8 * l + e + 1 ∧ l < i ∧ e < 8 ∧
    (l, i, e) ∈ ruRels := by
  intro i hi
  interval_cases i
  · exact Or.inl rfl
  · exact Or.inr ⟨0, 1, rfl, by norm_num, by norm_num, by decide⟩
  · exact Or.inr ⟨1, 1, rfl, by norm_num, by norm_num, by decide⟩
  · exact Or.inl rfl

theorem rep_x : Rep 4060 ruX (gp3 0) := by
  rw [ruX, arrE (by norm_num)]
  exact rep3' (by norm_num)

theorem getC {k : Nat} (hk : k < 2160) :
    (ruCCert ()).pts[k]! = treeArr 4060 ruGs TC.P TC.L k := by
  rw [ptsC, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem tail : ptailOK 4060 (rawLevels 4060 ruS ruBase) ruBase ruX (pow5A 4060 ruX) ruRels
    (ruCCert ()).pts.toList ruBase.size 0 (idA 4060) = true := by
  refine ptailOK_of_ptK_ (p := 5) tcJ rep_x (repF3' (by norm_num)) (by decide) fr_ok bs_lt ?_
    (by norm_num) kTail
  intro a A ha hA ⟨j, hj, e⟩
  have hR : A ∈ ruP := gen_le hA
  have hm := csk_lt j hj
  unfold kc tc at e
  rw [← keyA_treeArr treeC hgC hgsC keys_lt hm] at e
  have hr := rep_treeArr treeC hgsC (TC.SK j) hm
  have hmem := (el_tree treeC hgC hgsC memC hm).2.2
  rw [CFSG.RankThree.Native.permOfArr_eq_of_rep hr] at hmem
  have he := key_faith ha hr hR hmem e
  rw [List.any_eq_true]
  refine ⟨(ruCCert ()).pts[TC.SK j]!, ?_, ?_⟩
  · rw [getElem!_pos _ _ (by rw [sizeC]; exact hm)]
    exact Array.getElem_mem_toList _
  · rw [getC hm, eqA_iff ha hr, he]

theorem cent : ruCentOK () = true := by
  have hx := rep_x
  have hxf : RepF 4060 (t3 0) (gp3 0) := repF3' (by norm_num)
  have hxm : gp3 0 ∈ ruP := mem3' (by norm_num)
  have h1 : validA 4060 ruX = true := by
    rw [ruX, arrE (by norm_num)]
    exact valid3' (by norm_num)
  have h2 : siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 ruX = true := by
    rw [ruX, arrE (by norm_num)]
    exact sift3' (by norm_num)
  have h3 : eqA 4060 (powArr 4060 ruX 3) (idA 4060) = true :=
    eqA_P (rep_powArr hx 3) rep_idA (RepF.powF hxf 3) RepF.one (ruP.pow_mem hxm 3) ruP.one_mem kCube
  have h4 : eqA 4060 ruX (idA 4060) = false := by
    cases e : eqA 4060 ruX (idA 4060)
    · rfl
    · have he := (eqA_iff hx rep_idA).1 e
      have := eqOnL_of_eq bs_lt hxf (he ▸ RepF.one)
      have hk := kNe
      rw [this] at hk
      exact absurd hk (by decide)
  have h5 : relsOK 4060 ruBase ruX ruRels = true := by
    have hb : ∀ r ∈ ruRels, ruBase[r.1]! < 4060 := by decide
    unfold relsOK
    rw [List.all_eq_true]
    intro r hr
    have h := List.all_eq_true.1 kRels r hr
    rw [(rep_powArr hx r.2.2).apply (hb r hr), ← (RepF.powF hxf r.2.2) _ (hb r hr)]
    exact h
  have h8 : allLt ruGs.size (fun k => commA 4060 ruGs[k]! ruX) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := by simpa [ruGs] using hk
    rw [gC_get hk2]
    exact eqA_P (rep_compA (rep3' (by omega)) hx) (rep_compA hx (rep3' (by omega)))
      ((repF3' (k := 1 + k) (by omega)).comp hxf) (hxf.comp (repF3' (k := 1 + k) (by omega)))
      (ruP.mul_mem (mem3' (by omega)) hxm) (ruP.mul_mem hxm (mem3' (by omega)))
      (Orb.allN_iff.1 kComm k hk2)
  have h9 : allLt ruGs.size
      (fun k => siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 ruGs[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := by simpa [ruGs] using hk
    rw [gC_get hk2]
    exact sift3' (by omega)
  unfold ruCentOK
  rw [h1, h2, h3, h4, h5, enumC, sizeC, h8, h9, tail]
  rfl

@[expose] noncomputable def gpy (k : Nat) : Equiv.Perm (Fin 4060) := gp3 (3 + k)

theorem gY_get {k : Nat} (hk : k < 2) : ruSylGs[k]! = unpack 4060 12 (R3.F (3 + k)) := by
  rw [← arrE (by omega)]
  interval_cases k <;> rfl

theorem hgsY : ∀ k < 2, Rep 4060 ruSylGs[k]! (gpy k) := fun k hk => by
  rw [gY_get hk]
  exact rep3' (by omega)

theorem hgY : ∀ k < 2, RepF 4060 (gy k) (gpy k) := fun k hk => repF3' (k := 3 + k) (by omega)

theorem memY : ∀ k < 2, gpy k ∈ ruP := fun k hk => mem3' (by omega)

theorem treeY : TreeOK 2 27 TY.P TY.L := treeOK_of fun i hi h0 => by
  have h := Orb.allN_iff.1 kTreeY i hi
  rwa [CFSG.KC.HeLoc.beq_zero_false h0] at h

theorem edgesY : ∀ i < 27, ∀ k < 2, EY i k < 27 ∧
    treeArr 4060 ruSylGs TY.P TY.L (EY i k) =
      compA 4060 ruSylGs[k]! (treeArr 4060 ruSylGs TY.P TY.L i) :=
  edges_of_edgeAtK treeY hgY hgsY hmul memY (q0_iff memY) q0_lt bs_lt hF2
    fun i hi => Orb.allN_iff.1 kEdgeY i hi

theorem keyY : ∀ a < 27, ∀ b < 27, keyA 4060 ruKeys (treeArr 4060 ruSylGs TY.P TY.L a) =
    keyA 4060 ruKeys (treeArr 4060 ruSylGs TY.P TY.L b) → a = b := by
  have hk := keys_inj_of_sortAtK (key := ky) fun j hj => Orb.allN_iff.1 kSortY j hj
  intro a ha b hb e
  rw [keyA_treeArr treeY hgY hgsY keys_lt ha, keyA_treeArr treeY hgY hgsY keys_lt hb] at e
  exact hk a ha b hb e

theorem ptsY : (ruSylCert ()).pts =
    Array.ofFn (n := 27) fun i => treeArr 4060 ruSylGs TY.P TY.L i.val :=
  enumBfs_tree treeY hgsY (by simp [ruSylGs]) (by norm_num) (by norm_num) keyY edgesY kReplayY

theorem enumY : enumOK 4060 ruSylGs ruKeys (ruSylCert ()) = true :=
  enumOK_tree treeY hgsY (by simp [ruSylGs]) (by norm_num) (by norm_num) keyY edgesY

theorem sizeY : (ruSylCert ()).pts.size = 27 := by rw [ptsY, Array.size_ofFn]

theorem elY : ∀ i < 27, ElF ruP (ruSylCert ()).pts[i]! (ty i) := fun i hi => by
  rw [ptsY, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact el_tree treeY hgY hgsY memY hi

theorem sylow : ruSylowOK () = true := by
  have hx := rep_x
  have hxf : RepF 4060 (t3 0) (gp3 0) := repF3' (by norm_num)
  have hxm : gp3 0 ∈ ruP := mem3' (by norm_num)
  have h3 : allLt ruSylGs.size
      (fun k => siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 ruSylGs[k]!) = true := by
    rw [allLt_iff]
    intro k hk
    have hk2 : k < 2 := by simpa [ruSylGs] using hk
    rw [gY_get hk2]
    exact sift3' (by omega)
  have h4 : allLt (ruSylCert ()).pts.size (fun k => eqA 4060 (ruSylCert ()).pts[k]! (idA 4060) ||
      ruConjs.any fun g => validA 4060 g && siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 g &&
        eqA 4060 (conjA 4060 g (ruSylCert ()).pts[k]!) ruX) = true := by
    rw [allLt_iff]
    intro k hk
    rw [sizeY] at hk
    obtain ⟨hv, hr, hm⟩ := elY k hk
    have hrep := rep_of_validA hv
    have hs := Orb.allN_iff.1 kSyl k hk
    cases e : eqOnL bs (ty k) (fun y => y)
    · rw [e] at hs
      obtain ⟨j, hj, hje⟩ := exists_of_anyF hs
      rw [Bool.or_eq_true]
      right
      rw [List.any_eq_true]
      refine ⟨ruArr3 (5 + j), List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, ?_⟩
      have hs3 : siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 (unpack 4060 12 (R3.F (5 + j))) =
          true := sift3' (by omega)
      rw [arrE (by omega), valid3' (by omega), hs3, Bool.true_and, Bool.true_and]
      have hc := rep_conjA (valid3' (k := 5 + j) (by omega)) hrep
      have hcf : RepF 4060 (fun y => t3 (Nat.add 5 j) (ty k (i3 (Nat.add 5 j) y)))
          (gp3 (5 + j) * permOfArr 4060 (ruSylCert ()).pts[k]! * (gp3 (5 + j))⁻¹) := by
        rw [mul_assoc]
        exact (repF3' (k := 5 + j) (by omega)).comp (hr.comp (repF3i' (k := 5 + j) (by omega)))
      exact eqA_P hc hx hcf hxf
        (ruP.mul_mem (ruP.mul_mem (mem3' (by omega)) hm) (ruP.inv_mem (mem3' (by omega)))) hxm hje
    · rw [Bool.or_eq_true]
      left
      exact eqA_P hrep rep_idA hr RepF.one hm ruP.one_mem e
  unfold ruSylowOK
  rw [enumY, sizeY, h3]
  rw [sizeY] at h4
  rw [h4]
  rfl

theorem ruF_lt : ∀ p ∈ ThetaSpor.ruF, p < 4060 := by decide

theorem act_fix : allLt 4060 (fun i => (ruX[i]! == i) == ThetaSpor.ruF.contains i) = true := by
  rw [allLt_iff]
  intro i hi
  have hk := Orb.allN_iff.1 kFix i hi
  rw [ruX, arrE (by norm_num), unpackGet hi, beq_eq_nbeq]
  have e3 : pg 12 (mask 12) (R3.F 0) i = t3 0 i := rfl
  rw [e3]
  cases hb : Nat.beq (t3 0 i) i
  · rw [hb] at hk
    change (!ThetaSpor.ruF.contains i) = true at hk
    rw [Bool.not_eq_true'] at hk
    rw [hk]
    rfl
  · rw [hb] at hk
    change ThetaSpor.ruF.contains i = true at hk
    rw [hk]
    rfl

theorem act_ker : allLt (ruCCert ()).pts.size (fun k =>
    !(ThetaSpor.ruF.all fun p => ((ruEl k)[p]!) == p) || eqA 4060 (powArr 4060 (ruEl k) 3) (idA 4060)) =
    true := by
  rw [allLt_iff]
  intro k hk
  rw [sizeC] at hk
  obtain ⟨hv, hr, hm⟩ := elC k hk
  have hrep := rep_of_validA hv
  have hall : (ThetaSpor.ruF.all fun p => ((ruEl k)[p]!) == p) = ThetaSpor.ruF.all fun p => Nat.beq (tc k p) p := by
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, List.all_eq_true]
    refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩
    · have e := h p hp
      rw [ruEl, hrep.apply (ruF_lt p hp), ← hr p (ruF_lt p hp), beq_eq_nbeq] at e
      exact e
    · rw [ruEl, hrep.apply (ruF_lt p hp), ← hr p (ruF_lt p hp), beq_eq_nbeq]
      exact h p hp
  have hk' := Orb.allN_iff.1 kKer k hk
  rw [hall]
  cases e : ThetaSpor.ruF.all fun p => Nat.beq (tc k p) p
  · rfl
  · rw [e] at hk'
    rw [Bool.not_true, Bool.false_or]
    exact eqA_P (rep_powArr hrep 3) rep_idA (RepF.powF hr 3) RepF.one (ruP.pow_mem hm 3)
      ruP.one_mem hk'

theorem act_r {l : Nat} (hl : l < 2) {R : Array Nat}
    (h : ∀ i < 10, (ThetaSpor.ruF.idxOf (t3 (1 + l) ThetaSpor.ruF[i]!) == R[i]!) = true) :
    allLt 10 (fun i => ThetaSpor.ruF.idxOf ((ruGs[l]!)[ThetaSpor.ruF[i]!]!) == R[i]!) = true := by
  rw [allLt_iff]
  intro i hi
  have hp : ThetaSpor.ruF[i]! < 4060 := by interval_cases i <;> decide
  rw [gC_get hl, unpackGet hp]
  exact h i hi

theorem bind_ofT : BindA 10 4 tenGs ET.ng ET.G :=
  bind_of (by decide +kernel) (Nat.eq_of_beq_eq_true nT.1) bT

theorem eT : enumOK 10 #[ruR0, ruR1] [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] (ruTenCert ()) = true ∧
    (ruTenCert ()).pts.size = ET.N ∧
    ∀ i < ET.N, (ruTenCert ()).pts[i]! = unpack 10 4 (ET.T i) := by
  have hk : keys10.toList = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] := by decide +kernel
  have hps : ∀ p ∈ keys10.toList, p < 10 := by
    rw [hk]
    decide
  have h := enum_of (fuel := 800) bind_ofT (perm_of (Nat.eq_of_beq_eq_true nT.1) pT) ET.ok hps
    ET.keys (by decide +kernel)
  rw [hk] at h
  exact h

theorem act_two : allLt 10 (fun a => allLt 10 fun b => a == b ||
    (allLt (ruTenCert ()).pts.size (fun k => !(((ruTenCert ()).pts[k]!)[0]! == a &&
      ((ruTenCert ()).pts[k]!)[1]! == b)) == false)) = true := by
  have hN : ET.N = 720 := Nat.eq_of_beq_eq_true nT.2
  obtain ⟨-, hs, hp⟩ := eT
  rw [allLt_iff]
  intro a ha
  rw [allLt_iff]
  intro b hb
  have h := Orb.allN_iff.1 (Orb.allN_iff.1 kTwo a ha) b hb
  rw [beq_eq_nbeq]
  cases e : Nat.beq a b
  · rw [e] at h
    change anyF 720 _ = true at h
    obtain ⟨k, hk, hke⟩ := exists_of_anyF h
    rw [Bool.false_or]
    have hkN : k < ET.N := by rw [hN]; exact hk
    have hf : allLt (ruTenCert ()).pts.size (fun k => !(((ruTenCert ()).pts[k]!)[0]! == a &&
        ((ruTenCert ()).pts[k]!)[1]! == b)) = false := by
      rw [Bool.eq_false_iff]
      intro hall
      have h1 := allLt_iff.1 hall k (by rw [hs]; exact hkN)
      rw [hp k hkN, unpack_get (by norm_num), unpack_get (by norm_num), beq_eq_nbeq,
        beq_eq_nbeq] at h1
      rw [(bAnd_iff _ _).1 hke |>.1, (bAnd_iff _ _).1 hke |>.2] at h1
      exact absurd h1 (by decide)
    rw [hf]
    rfl
  · rfl

theorem action : ruActionOK () = true := by
  obtain ⟨he, hs, -⟩ := eT
  have hN : ET.N = 720 := Nat.eq_of_beq_eq_true nT.2
  unfold ruActionOK
  rw [act_fix, act_ker, act_r (l := 0) (by norm_num) kR0, act_r (l := 1) (by norm_num) kR1,
    act_two, he, hs, hN]
  rfl

theorem ruThree_ok : ruThreeOK () = true := by
  unfold ruThreeOK
  rw [cent, sylow, action]
  rfl

end Ru

end CertificateChecks.KernelTc.Ru

end
