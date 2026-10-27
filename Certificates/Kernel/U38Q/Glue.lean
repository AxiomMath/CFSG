module

public import Certificates.Kernel.U38Q.Checks
public import Certificates.Kernel.U38Q.NoE81Checks
public import Certificates.Kernel.SchreierFam.C188001F
public import Certificates.Kernel.U38.Facts
public import CFSG.Certificates.Kernel.U38QKSound
public import CFSG.Certificates.Kernel.Spor.RawSiftKConv
public import CFSG.Certificates.Kernel.PGrpMul
public import Certificates.Data.HuppertU38Q.NoE81

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Q

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
  CFSG.KC.B3S3K CFSG.KC.K426K CFSG.KC.U38QK CFSG.KC.U38NoE81K CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.Certificates.Native CFSG.RankThree.PartTwo.Sec4.Item434U38 U38Sylow
open CFSG.Monster.B.Co2 (allLt_iff permOfArr)

theorem hw : szOK 513 10 = true := q211SzOK

theorem perm3 {k : ℕ} (hk : k < 3) : permB 513 10 (QH.F k) = true := allN_spec q211Perm k hk

theorem gen_eq {k : ℕ} (hk : k < 3) : qGens[k]! = unpack 513 10 (QH.F k) := by
  rw [qGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn, QH.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound QH.all k hk

theorem nums' : QE.N = 729 ∧ QE.ng = 3 :=
  ⟨Nat.eq_of_beq_eq_true q211Nums.1, Nat.eq_of_beq_eq_true q211Nums.2⟩

theorem G_eq {k : ℕ} (hk : k < 3) : QE.G k = QH.F k :=
  Nat.eq_of_beq_eq_true (allN_spec q211Gens k hk)

theorem bindQ : BindA 513 10 qGens QE.ng QE.G := by
  rw [nums'.2]
  refine ⟨rfl, fun k hk => ?_⟩
  rw [gen_eq hk, G_eq hk]

theorem permG : ∀ k < QE.ng, permB 513 10 (QE.G k) = true := fun k hk => by
  rw [nums'.2] at hk
  rw [G_eq hk]
  exact perm3 hk

theorem hps : ∀ p ∈ keyPts, p < 513 := by decide

theorem enumQ : enumOK 513 qGens keyPts (qCert ()) = true ∧ (qCert ()).pts.size = QE.N ∧
    ∀ i < QE.N, (qCert ()).pts[i]! = unpack 513 10 (QE.T i) :=
  enum_of (ps := keyPts) (fuel := 800) bindQ permG QE.ok hps QE.keys (by rw [nums'.1]; omega)

theorem sz : (qCert ()).pts.size = 729 := by rw [enumQ.2.1, nums'.1]

theorem iN {i : ℕ} (hi : i < 729) : i < QE.N := by rw [nums'.1]; exact hi

theorem getT {i : ℕ} (hi : i < 729) : (qCert ()).pts[i]! = unpack 513 10 (QE.T i) :=
  enumQ.2.2 i (iN hi)

theorem ppT {i : ℕ} (hi : i < 729) : PP 513 10 (QE.T i) := PP_pts QE.ok permG i (iN hi)

theorem permT {i : ℕ} (hi : i < 729) : permB 513 10 (QE.T i) = true := permB_of_pp (ppT hi)

theorem memT {i : ℕ} (hi : i < 729) :
    permOfArr 513 (unpack 513 10 (QE.T i)) ∈ Subgroup.closure (permsA 513 qGens) :=
  mem_of_pt hw hps enumQ.1 enumQ.2.1 enumQ.2.2 (iN hi)

theorem commAt_eq {a b : ℕ} (ha : a < 729) (hb : b < 729) :
    commAt (qCert ()).pts[a]! (qCert ()).pts[b]! = comK 513 10 [0, 167, 270] (QE.T a) (QE.T b) := by
  rw [getT ha, getT hb, commAt, eqA_keyCK hw hps enumQ.1 (permT ha) (permT hb) (permT hb)
    (permT ha) (memT ha) (memT hb) (memT hb) (memT ha)]
  rfl

theorem cube_eq {i : ℕ} (hi : i < 729) : cubeOne (qCert ()).pts[i]! = cubeK 513 10 (QE.T i) := by
  have p := permT hi
  have pp := CFSG.KC.PGrp.permB_pcomp hw p p
  rw [getT hi, cubeOne, comp_unpack' hw p p, comp_unpack' hw p pp,
    eqA_id hw (CFSG.KC.PGrp.permB_pcomp hw p pp)]
  rfl

theorem siftOK_eq {G : ℕ} (hG : PP 513 10 G) {nb : ℕ} {LR TRI : ℕ → ℕ} {BP : ℕ} :
    siftOK 513 10 nb LR TRI BP G =
      siftK 513 10 (mask 10) (513 * 10) (pidn 513 10) LR TRI BP nb 0 G := by
  obtain ⟨-, -, hG0, hGl⟩ := PF.canon_facts hG.1
  have e0 : Nat.shiftRight G (Nat.mul 513 10) = 0 := hG0
  have hr : allN 513 (fun i => Nat.blt (pg 10 (mask 10) G i) 513) = true :=
    Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hGl i hi)
  unfold siftOK
  rw [e0, hr]
  rfl

theorem siftX_eq {G : ℕ} (hG : PP 513 10 G) :
    siftA 513 (rawLevels 513 strong3 base3) base3 0 (unpack 513 10 G) =
      siftOK 513 10 4 KernelU38.UX.LR KernelU38.UX.TRI KernelU38.UX.BP G := by
  cases h : siftOK 513 10 4 KernelU38.UX.LR KernelU38.UX.TRI KernelU38.UX.BP G
  · rw [siftOK_eq hG] at h
    obtain ⟨-, -, hG0, hGl⟩ := PF.canon_facts hG.1
    exact Orb.siftA_false_of_K KernelU38.binds KernelU38.permX KernelU38.UX.hl hw hG0
      (Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (hGl i hi)) h
  · exact siftA_of_siftOK KernelU38.binds KernelU38.permX KernelU38.UX.hl h

theorem inX_eq : inX (qCert ()).pts (rawLevels 513 strong3 base3) = XI := by
  unfold inX
  rw [sz, ← sel_spec q211InX]
  apply List.filter_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [getT hi', siftX_eq (ppT hi')]

theorem genSift : allLt qGens.size
    (fun k => siftA 513 (rawLevels 513 strong1 base1) base1 0 qGens[k]!) = true := by
  rw [allLt_iff]
  intro k hk
  have hk3 : k < 3 := by simpa [qGens] using hk
  rw [gen_eq hk3]
  exact siftA_of_siftOK KernelSchreierFam.U38B.binds1 KernelSchreierFam.U38B.perm1
    KernelSchreierFam.U38C1.hl (allN_spec q211Sift1 k hk3)

theorem ltXI : ∀ i ∈ XI, i < 729 := fun i hi => by
  rw [← sel_spec q211InX] at hi
  exact List.mem_range.1 (List.mem_filter.1 hi).1

theorem ltL {W : List ℕ} (h : allL (fun j => Nat.blt j 729) W = true) : ∀ j ∈ W, j < 729 :=
  fun j hj => Nat.blt_eq.mp (List.all_eq_true.1 ((allL_eq _ _).symm.trans h) j hj)

theorem coset_eq {r : ℕ} (hr : r < 2) {W C : List ℕ}
    (hW : pairK (fun i j => Nat.beq (pcomp 513 10 (mask 10) (QH.F r) (QE.T i)) (QE.T j)) XI W =
      true)
    (hWl : allL (fun j => Nat.blt j 729) W = true)
    (hC : selL (fun j => cubeK 513 10 (QE.T j)) W C = true) :
    cosetCubes qGens[r]! (qCert ()).pts XI = C.map fun j => (qCert ()).pts[j]! := by
  have hm : XI.map (fun i => compA 513 qGens[r]! (qCert ()).pts[i]!) =
      W.map fun j => (qCert ()).pts[j]! :=
    map_eq_of_forall₂ (forall₂_of_pairK hW) fun i hi j hj e => by
      rw [getT (ltXI i hi), getT (ltL hWl j hj), gen_eq (by omega),
        comp_unpack' hw (perm3 (by omega)) (permT (ltXI i hi)), Nat.eq_of_beq_eq_true e]
  unfold cosetCubes
  rw [hm, List.filter_map, ← filter_of_selL hC]
  congr 1
  apply List.filter_congr
  intro j hj
  exact cube_eq (ltL hWl j hj)

theorem ltC {W C : List ℕ} (hWl : allL (fun j => Nat.blt j 729) W = true)
    (hC : selL (fun j => cubeK 513 10 (QE.T j)) W C = true) : ∀ j ∈ C, j < 729 :=
  fun j hj => by
    rw [← filter_of_selL hC] at hj
    exact ltL hWl j (List.mem_filter.1 hj).1

theorem noComm_eq : noCommuting (CA.map fun j => (qCert ()).pts[j]!)
    (CB.map fun j => (qCert ()).pts[j]!) = true := by
  have h := q211NoComm
  unfold noCommK at h
  rw [allL_eq, List.all_eq_true] at h
  unfold noCommuting
  rw [List.all_map, List.all_eq_true]
  intro a ha
  have h2 := h a ha
  rw [Orb.strictB_eq, allL_eq, List.all_eq_true] at h2
  have la := ltC q211WLt.1 q211CA a ha
  simp only [Function.comp_apply]
  rw [List.all_map, List.all_eq_true]
  intro b hb
  have h3 := h2 b hb
  rw [Orb.strictB_eq] at h3
  have lb := ltC q211WLt.2 q211CB b hb
  simp only [Function.comp_apply]
  rw [getT la, getT lb, eqA_keyCK hw hps enumQ.1 (permT la) (permT lb) (permT lb) (permT la)
    (memT la) (memT lb) (memT lb) (memT la)]
  exact h3

theorem sylow_true : u38SylowCheck () = true := by
  have hA := coset_eq (r := 0) (by norm_num) q211WA q211WLt.1 q211CA
  have hB := coset_eq (r := 1) (by norm_num) q211WB q211WLt.2 q211CB
  have hl : XI.length = 81 := Nat.eq_of_beq_eq_true q211Lens.1
  unfold u38SylowCheck
  simp only [inX_eq, hA, hB, enumQ.1, sz, genSift, hl, noComm_eq, beq_self_eq_true,
    Bool.and_self]

theorem ltCU : ∀ u ∈ CU, u < 729 := fun u hu => by
  rw [← sel_spec q211CU] at hu
  exact List.mem_range.1 (List.mem_filter.1 hu).1

theorem cu_eq : ((List.range (qCert ()).pts.size).filter fun i => cubeOne (qCert ()).pts[i]!) =
    CU := by
  rw [sz, ← sel_spec q211CU]
  apply List.filter_congr
  intro i hi
  exact cube_eq (List.mem_range.1 hi)

theorem cen_len {u : ℕ} (hu : u < 729) :
    (cenOf (qCert ()).pts u).length = cenK 513 10 [0, 167, 270] QE.T 729 u := by
  unfold cenOf cenK
  rw [Orb.strictN_eq, cntK_eq_length, sz]
  congr 1
  apply List.filter_congr
  intro j hj
  rw [Orb.strictB_eq, commAt_eq hu (List.mem_range.1 hj)]

theorem cenOK_facts {u v : ℕ} (h : cenOK 513 10 [0, 167, 270] QE.T 729 u v = true) :
    cenK 513 10 [0, 167, 270] QE.T 729 u = Nat.div v 1048576 ∧
      (cenK 513 10 [0, 167, 270] QE.T 729 u = 81 → ∃ j < 729, ∃ k < 729,
        comK 513 10 [0, 167, 270] (QE.T u) (QE.T j) = true ∧
        comK 513 10 [0, 167, 270] (QE.T u) (QE.T k) = true ∧
        comK 513 10 [0, 167, 270] (QE.T j) (QE.T k) = false) := by
  simp only [cenOK, Orb.strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  refine ⟨Nat.eq_of_beq_eq_true h1, fun h81 => ?_⟩
  cases hc : Nat.beq (cenK 513 10 [0, 167, 270] QE.T 729 u) (nat_lit 81)
  · rw [h81] at hc
    exact absurd hc (by decide)
  · rw [hc] at h2
    dsimp only at h2
    simp only [Orb.bAnd_eq, Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at h2
    obtain ⟨hj, hk, a, b, c⟩ := h2
    exact ⟨_, hj, _, hk, a, b, c⟩

theorem noE81_true : noE81Check () = true := by
  have F := forall₂_of_pairK q211CW
  unfold noE81Check noE81Pts
  simp only [cu_eq]
  rw [Bool.and_eq_true]
  constructor
  · rw [decide_eq_true_eq, List.filter_map, List.length_map]
    have e : (CU.filter ((fun p : ℕ × List ℕ => decide (243 ≤ p.2.length)) ∘
        fun i => (i, cenOf (qCert ()).pts i))).length =
        (CW.filter fun v => Nat.ble 243 (Nat.div v 1048576)).length :=
      filter_length_of_forall₂ F fun u hu v _ e => by
        simp only [Function.comp_apply]
        rw [cen_len (ltCU u hu), (cenOK_facts e).1, Bool.eq_iff_iff, decide_eq_true_iff,
          Nat.ble_eq]
    rw [e, ← bigK_eq]
    exact Nat.le_of_ble_eq_true q211Big
  · rw [List.all_map, List.all_eq_true]
    intro u hu
    obtain ⟨v, -, e⟩ := exists_of_forall₂ F u hu
    have lu := ltCU u hu
    simp only [Function.comp_apply, Bool.or_eq_true, bne_iff_ne, ne_eq]
    by_cases h81 : cenK 513 10 [0, 167, 270] QE.T 729 u = 81
    · right
      obtain ⟨j, hj, k, hk, huj, huk, hjk⟩ := (cenOK_facts e).2 h81
      have mj : j ∈ cenOf (qCert ()).pts u := by
        unfold cenOf
        rw [List.mem_filter, List.mem_range, sz, commAt_eq lu hj]
        exact ⟨hj, huj⟩
      have mk : k ∈ cenOf (qCert ()).pts u := by
        unfold cenOf
        rw [List.mem_filter, List.mem_range, sz, commAt_eq lu hk]
        exact ⟨hk, huk⟩
      unfold nonAbelianAt
      rw [List.any_eq_true]
      refine ⟨j, mj, List.any_eq_true.2 ⟨k, mk, ?_⟩⟩
      rw [commAt_eq hj hk, hjk]
      rfl
    · left
      rw [cen_len lu]
      exact h81

end CertificateChecks.KernelU38Q

end
