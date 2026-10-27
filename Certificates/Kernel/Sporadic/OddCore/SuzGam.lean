module

public import Certificates.Kernel.Sporadic.OddCore.SuzGamM
public import Certificates.Kernel.Sporadic.OddCore.SuzGamW
public import Certificates.Kernel.Sporadic.OddCore.SuzGamI0
public import Certificates.Kernel.Sporadic.OddCore.SuzGamI1
public import Certificates.Kernel.Sporadic.OddCore.SuzGamI2
public import Certificates.Kernel.Sporadic.OddCore.SuzGamI3
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR0
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR1
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR2
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR3
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR4
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR5
public import Certificates.Kernel.Sporadic.OddCore.SuzGamR6
public import Certificates.Kernel.Sporadic.OddCore.Suz2308
public import CFSG.Certificates.Kernel.SuzGamma2294Sound
public import CFSG.Sporadic.SuzOddCore.GammaStageInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.SGam

open CFSG.Sporadic.SuzOddCore CFSG.KC.Enum CFSG.KC.G2294 CFSG.KS.Raw CFSG.KS.Raw.Orb
open CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore.Native CertificateChecks.KernelSpor

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem nbeq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem blk_all {f : Nat → Bool} (h : ∀ s < 358, blk f s = true) : ∀ x < 22880, f x = true := by
  intro x hx
  have h2 := CFSG.KC.Pack.allBlk_spec (h (x / 64) (by omega)) (x % 64) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 64 (x / 64)) (x % 64) = x := by
    change 64 * (x / 64) + x % 64 = x
    omega
  have hb : Nat.blt x 22880 = true := Eq.mpr Nat.blt_eq hx
  rw [e, hb] at h2
  exact h2

theorem blkL_all {f : Nat → Bool} (h : ∀ s < 23, blkL f s = true) : ∀ x < 22880, f x = true := by
  intro x hx
  have h2 := CFSG.KC.Pack.allN_spec (h (x / 1024) (by omega)) (x % 1024)
    (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 1024 (x / 1024)) (x % 1024) = x := by
    change 1024 * (x / 1024) + x % 1024 = x
    omega
  have hb : Nat.blt x 22880 = true := Eq.mpr Nat.blt_eq hx
  rw [strictB_eq, e, hb] at h2
  exact h2

theorem of23 {F : Nat → Nat → Bool} {m : Nat} (h : ∀ i < 23 * m, F (i / 23) (i % 23) = true) :
    ∀ j < m, ∀ s < 23, F j s = true := by
  intro j hj s hs
  have e1 : (23 * j + s) / 23 = j := by omega
  have e2 : (23 * j + s) % 23 = s := by omega
  have := h (23 * j + s) (by omega)
  rwa [e1, e2] at this

theorem gen_get {k x : Nat} (hk : k < 2) (hx : x < 22880) :
    (certArr k)[x]! = gp (SuzGamG k) x ∧ gp (SuzGamG k) x < 22880 := by
  have h := of23 (F := genL) (m := 2) (fun i hi => Gen.all i hi) k hk (x / 1024) (by omega)
  rw [genL, strictB_eq] at h
  have h2 := CFSG.KC.Pack.allN_spec h (x % 1024) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 1024 (x / 1024)) (x % 1024) = x := by
    change 1024 * (x / 1024) + x % 1024 = x
    omega
  have hb : Nat.blt x 22880 = true := Eq.mpr Nat.blt_eq hx
  rw [strictB_eq, e, hb] at h2
  have hg := Nat.eq_of_beq_eq_true h2
  have hc : (certArr k)[x]! = CFSG.KS.Row.rg 15 (CFSG.KS.mask 15) SuzCertT.F (Nat.mul 715 k) x := by
    rw [certArr_eq (by omega), CFSG.KS.Row.rowArr_get hx]
    rfl
  refine ⟨by rw [hc, hg], ?_⟩
  rw [hg]
  exact S2308.cert_rngF (k := k) (by omega) x hx

theorem certArr_size {k : Nat} (hk : k < 2) : (certArr k).size = 22880 := by
  rw [certArr_eq (by omega), CFSG.KS.Row.size_rowArr]

theorem gens_eq : ∀ k < 2, (#[certArr 0, certArr 1] : Array (Array Nat))[k]! =
    unpack 22880 15 (SuzGamG k) := by
  intro k hk
  have e : (#[certArr 0, certArr 1] : Array (Array Nat))[k]! = certArr k := by
    interval_cases k <;> rfl
  rw [e]
  refine S2308.arr_eq (certArr_size hk) (by rw [unpack, Array.size_ofFn]) fun x hx => ?_
  rw [(gen_get hk hx).1, unpack_get hx]
  rfl

theorem rows : ∀ x < 22880, rowOK 22880 280 SuzGamR x = true := blk_all Row.all

theorem img_all {k : Nat} (hk : k < 2) : ∀ s < 358, img k s = true := by
  intro s hs
  interval_cases k
  · by_cases h : s < 179
    · exact I0.all s h
    · have hlt : s - 179 < 179 := by omega
      have hle : 179 ≤ s := by omega
      have := I1.all (s - 179) hlt
      have e : Nat.add (nat_lit 179) (s - 179) = s := Nat.add_sub_of_le hle
      rw [img0b, img0, e] at this
      exact this
  · by_cases h : s < 179
    · exact I2.all s h
    · have hlt : s - 179 < 179 := by omega
      have hle : 179 ≤ s := by omega
      have := I3.all (s - 179) hlt
      have e : Nat.add (nat_lit 179) (s - 179) = s := Nat.add_sub_of_le hle
      rw [img1b, img1, e] at this
      exact this

theorem imgs : ∀ k < 2, ∀ x < 22880, imgOK 22880 280 (SuzGamG k) SuzGamR x = true := by
  intro k hk
  refine blk_all fun s hs => ?_
  have := img_all hk s hs
  rw [img, strictB_eq] at this
  exact this

theorem root_eq : deltaOf zArr = CFSG.KC.N3153.decodeRow 280 (SuzGamR 0) := by
  rw [S2308.delta_eq, localDomain_eq]
  apply List.ext_getElem
  · simp only [Array.length_toList, unpack, Array.size_ofFn, CFSG.KC.N3153.decodeRow,
      List.length_map, List.length_range]
  · intro i h1 h2
    have hi : i < 280 := by
      simp only [Array.length_toList, unpack, Array.size_ofFn] at h1
      exact h1
    have hr := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec root i hi)
    rw [Array.getElem_toList, ← getElem!_pos _ i (by rw [unpack, Array.size_ofFn]; exact hi),
      unpack_get hi]
    simp only [CFSG.KC.N3153.decodeRow, List.getElem_map, List.getElem_range]
    rw [← hr]
    rfl

theorem graph : adjSearch 22880 #[certArr 0, certArr 1] (deltaOf zArr) =
      CFSG.KC.N3153.rowsArr 22880 280 SuzGamR ∧
    adjOK 22880 #[certArr 0, certArr 1] (CFSG.KC.N3153.rowsArr 22880 280 SuzGamR)
      (deltaOf zArr) = true :=
  graph_sound (ng := 2) (G := SuzGamG) (T := SuzGamT) (by norm_num) (by norm_num) (by norm_num)
    rfl gens_eq rows imgs (blkL_all Tree.all) (CFSG.KC.Pack.allN_spec sym0) root_eq

theorem nbr_eq : gammaNbr = CFSG.KC.N3153.rowsArr 22880 280 SuzGamR := graph.1

theorem adj : adjOK 22880 #[certArr 0, certArr 1] gammaNbr (deltaOf zArr) = true := by
  rw [nbr_eq]
  exact graph.2

@[expose] noncomputable def col (j : Nat) : Array Nat := unpackC 22880 (SuzGamC j)

theorem col_size (j : Nat) : (col j).size = 22880 := by rw [col, unpackC, Array.size_ofFn]

theorem gammaE0_eq : gammaE0 = stepT 22880 gammaNbr (idA 22880)
    (stepT 22880 gammaNbr (idA 22880) (initT 22880 (idA 22880) [0])) := by
  rw [gammaE0, colourT, refineT, refineT, refineT]

theorem refineT_one (c : Array Nat) :
    refineT 22880 gammaNbr (idA 22880) c 1 = stepT 22880 gammaNbr (idA 22880) c := by
  rw [refineT, refineT]

theorem refineT_two (c : Array Nat) :
    refineT 22880 gammaNbr (idA 22880) c 2 =
      stepT 22880 gammaNbr (idA 22880) (stepT 22880 gammaNbr (idA 22880) c) := by
  rw [refineT, refineT, refineT]

theorem stage_succ (s : Nat) : gammaStage (s + 1) = refineT 22880 gammaNbr (idA 22880)
    (gammaBaseCol (gammaStage s) (gammaMover s) gammaE0) (gammaRounds.getD s 0) := by
  rw [gammaStage]

theorem hash_all {j : Nat} (hj : j < 7) :
    ∀ v < 22880, hashOK (SuzGamC (hashSrc j)) (SuzGamC (Nat.add 13 j)) v = true := by
  refine blkL_all fun s hs => ?_
  have := of23 (F := hashL) (m := 7) (fun i hi => Hash.all i hi) j hj s hs
  rw [hashL, strictB_eq, strictB_eq] at this
  exact this

theorem stepK {a h b : Nat} (hr : ∀ s < 358, rnd a h b s = true)
    (hh : ∀ v < 22880, hashOK (SuzGamC a) (SuzGamC h) v = true) :
    stepT 22880 gammaNbr (idA 22880) (col a) = col b := by
  rw [nbr_eq]
  refine step_sound (by norm_num) rows hh (blk_all fun s hs => ?_)
  have := hr s hs
  rw [rnd, strictB_eq, strictB_eq, strictB_eq] at this
  exact this

theorem initT_get {v : Nat} (hv : v < 22880) :
    (initT 22880 (idA 22880) [0])[v]! = if v = 0 then 3 else 1 := by
  rw [initT, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ hv]
  simp only [idA_get hv, beq_self_eq_true, if_true]
  by_cases h0 : v = 0
  · subst h0
    rfl
  · have e : [0].idxOf? v = none := List.idxOf?_eq_none_iff.2 (by simpa [eq_comm] using h0)
    rw [e, if_neg h0]
    rfl

theorem init_eq : initT 22880 (idA 22880) [0] = col 1 := by
  refine S2308.arr_eq (by rw [initT, Array.size_ofFn]) (col_size 1) fun v hv => ?_
  have hi := Nat.eq_of_beq_eq_true (blkL_all (f := initOK (SuzGamC 1)) (fun s hs => by
    have := Init.all s hs
    rw [initL, strictB_eq] at this
    exact this) v hv)
  rw [col, unpackC_get hv, hi, initT_get hv]
  by_cases h0 : v = 0
  · subst h0
    rfl
  · rw [if_neg h0, nbeq_false h0]

theorem e0_eq : gammaE0 = col 3 := by
  rw [gammaE0_eq, init_eq, stepK R0.all (hash_all (j := 0) (by norm_num)),
    stepK R1.all (hash_all (j := 1) (by norm_num))]

theorem gamma_mover0 : gammaMover 0 = idA 22880 := by
  rw [gammaMover, gammaWords, List.getD_cons_zero, gammaWordArr, List.foldr_nil]

theorem gamma_mover1 : gammaMover 1 = compA 22880 (certArr 0) (idA 22880) := by
  rw [gammaMover, gammaWords, List.getD_cons_succ, List.getD_cons_zero, gammaWordArr,
    List.foldr_cons, List.foldr_nil]

theorem gamma_mover2 :
    gammaMover 2 = compA 22880 (certArr 1) (compA 22880 (certArr 1) (idA 22880)) := by
  rw [gammaMover, gammaWords, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero,
    gammaWordArr, List.foldr_cons, List.foldr_cons, List.foldr_nil]

theorem gamma_mover3 : gammaMover 3 =
    compA 22880 (certArr 0) (compA 22880 (certArr 1) (compA 22880 (certArr 1) (idA 22880))) := by
  rw [gammaMover, gammaWords, List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_cons_zero, gammaWordArr, List.foldr_cons, List.foldr_cons, List.foldr_cons,
    List.foldr_nil]

theorem mv_eq (G0 G1 t v : Nat) : mv G0 G1 t v =
    if t = 0 then v else if t = 1 then gp G0 v else if t = 2 then gp G1 (gp G1 v)
    else gp G0 (gp G1 (gp G1 v)) := by
  unfold mv
  rw [strictN_eq]
  by_cases h0 : t = 0
  · subst h0
    rfl
  · rw [if_neg h0, nbeq_false h0]
    by_cases h1 : t = 1
    · subst h1
      rfl
    · rw [if_neg h1, nbeq_false h1]
      by_cases h2 : t = 2
      · subst h2
        rfl
      · rw [if_neg h2, nbeq_false h2]

theorem mover_get {t v : Nat} (ht : t < 4) (hv : v < 22880) :
    (gammaMover t)[v]! = mv (SuzGamG 0) (SuzGamG 1) t v ∧ mv (SuzGamG 0) (SuzGamG 1) t v < 22880 := by
  have g0 := fun x (hx : x < 22880) => gen_get (k := 0) (by norm_num) hx
  have g1 := fun x (hx : x < 22880) => gen_get (k := 1) (by norm_num) hx
  rw [mv_eq]
  interval_cases t
  · rw [gamma_mover0, idA_get hv]
    exact ⟨rfl, hv⟩
  · rw [gamma_mover1, compA_get hv, idA_get hv]
    exact g0 v hv
  · rw [gamma_mover2, compA_get hv, compA_get hv, idA_get hv, (g1 v hv).1, (g1 _ (g1 v hv).2).1]
    exact ⟨rfl, (g1 _ (g1 v hv).2).2⟩
  · rw [gamma_mover3, compA_get hv, compA_get hv, compA_get hv, idA_get hv, (g1 v hv).1,
      (g1 _ (g1 v hv).2).1, (g0 _ (g1 _ (g1 v hv).2).2).1]
    exact ⟨rfl, (g0 _ (g1 _ (g1 v hv).2).2).2⟩

theorem base_eq {t a b : Nat} (ht : t < 4) (hab : baseSrc t = (a, b)) :
    gammaBaseCol (col a) (gammaMover t) (col 3) = col b := by
  refine S2308.arr_eq (by rw [gammaBaseCol, Array.size_ofFn]) (col_size _) fun v hv => ?_
  have hb := blkL_all (f := baseOK (mv (SuzGamG 0) (SuzGamG 1) t) (SuzGamC a) (SuzGamC 3)
      (SuzGamC b)) (fun s hs => by
    have := of23 (F := baseL) (m := 4) (fun i hi => Base.all i hi) t ht s hs
    rw [baseL, strictB_eq, strictB_eq, strictB_eq, strictB_eq, strictB_eq, hab] at this
    exact this) v hv
  have hm := mover_get ht hv
  rw [gammaBaseCol, CFSG.Monster.B.Co2.getElem!_ofFn_nat _ hv]
  simp only
  rw [col, col, col, unpackC_get hv, unpackC_get hv, hm.1, unpackC_get hm.2,
    Nat.eq_of_beq_eq_true hb]
  rfl

theorem stage0_eq : gammaStage 0 = col 0 := by
  refine S2308.arr_eq (by rw [gammaStage, Array.size_replicate]) (col_size 0) fun v hv => ?_
  have h := Nat.eq_of_beq_eq_true (blkL_all (f := fun v => Nat.beq (cs (SuzGamC 0) v) 1)
    (fun s hs => by
    have := One.all s hs
    rw [oneL, strictB_eq] at this
    exact this) v hv)
  rw [gammaStage, getElem!_pos _ _ (by rw [Array.size_replicate]; exact hv),
    Array.getElem_replicate, col, unpackC_get hv, h]

theorem rounds0 : gammaRounds.getD 0 0 = 0 := rfl
theorem rounds1 : gammaRounds.getD 1 0 = 2 := rfl
theorem rounds2 : gammaRounds.getD 2 0 = 1 := rfl
theorem rounds3 : gammaRounds.getD 3 0 = 2 := rfl

theorem stage1_eq : gammaStage 1 = col 4 := by
  rw [stage_succ, rounds0, refineT, stage0_eq, e0_eq]
  exact base_eq (t := 0) (by norm_num) rfl

theorem stage2_eq : gammaStage 2 = col 7 := by
  rw [stage_succ, rounds1, refineT_two, stage1_eq, e0_eq, base_eq (t := 1) (by norm_num) rfl,
    stepK R2.all (hash_all (j := 2) (by norm_num)), stepK R3.all (hash_all (j := 3) (by norm_num))]

theorem stage3_eq : gammaStage 3 = col 9 := by
  rw [stage_succ, rounds2, refineT_one, stage2_eq, e0_eq, base_eq (t := 2) (by norm_num) rfl]
  exact stepK R4.all (hash_all (j := 4) (by norm_num))

theorem stage4_eq : gammaStage 4 = col 12 := by
  rw [stage_succ, rounds3, refineT_two, stage3_eq, e0_eq, base_eq (t := 3) (by norm_num) rfl,
    stepK R5.all (hash_all (j := 5) (by norm_num)), stepK R6.all (hash_all (j := 6) (by norm_num))]

theorem cell_le {j p b : Nat} (hp : p < 22880)
    (h : strictB (SuzGamC j) (fun C => Nat.ble (cellCnt 22880 C (cs C p)) b) = true) :
    cellCount 22880 (col j) (col j)[p]! ≤ b := by
  rw [strictB_eq] at h
  rw [col, unpackC_get hp, ← cellCnt_eq]
  exact Nat.le_of_ble_eq_true h

theorem facts2294 :
    adjOK 22880 #[certArr 0, certArr 1] gammaNbr (deltaOf zArr) = true ∧ gammaStagesOK = true := by
  refine ⟨adj, ?_⟩
  have hm : allLt 4 (fun s => (gammaMover s)[s]! == 0) = true := by
    refine CFSG.Monster.B.Co2.allLt_iff.2 fun s hs => beq_iff_eq.2 ?_
    rw [(mover_get hs (by omega)).1, mv_eq]
    have h := movers
    simp only [CFSG.KS.bAnd_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    interval_cases s
    · rfl
    · exact Nat.eq_of_beq_eq_true h1
    · exact Nat.eq_of_beq_eq_true h2
    · exact Nat.eq_of_beq_eq_true h3
  have hi := inj
  rw [strictB_eq, strictB_eq] at hi
  simp only [gammaStagesOK, Bool.and_eq_true, decide_eq_true_eq]
  rw [stage1_eq, stage2_eq, stage3_eq, stage4_eq]
  exact ⟨⟨⟨⟨hm, cell_le (by norm_num) cell1⟩, cell_le (by norm_num) cell2⟩,
    cell_le (by norm_num) cell3⟩, inj_sound hi⟩

end CertificateChecks.KernelSpor.OddCore.SGam

end
