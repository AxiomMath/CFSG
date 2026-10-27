module

public import Certificates.Kernel.MonsterExist.Sparse
public import CFSG.Monster.Existence.Census.Rigid

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.RigidW

open CertificateChecks.MonsterExist.Sparse
open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Visible CFSG.Monster.Griess CFSG.Monster.AxisCount Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

@[expose] def monoRow (rm : Bool → ℕ → Bool × Bool × ℕ) (r : ℕ) : Terms :=
  [(Native.rowIdx (rm (Native.rowEta r) (Native.rowC r)).2.1
      (rm (Native.rowEta r) (Native.rowC r)).2.2,
    Native.sgnI (rm (Native.rowEta r) (Native.rowC r)).1)]

@[expose] def xiRow (r : ℕ) : Terms :=
  [false, true].flatMap fun f =>
    let α := Native.xiGammaN (Native.rowC r) f
    if α == 0 then []
    else (List.range 64).map fun ν =>
      let t := Native.xiGTerm (Native.rowEta r != f) (Native.rowC r) ν
      (Native.rowIdx t.2.1 t.2.2, α * Native.sgnI t.1)

@[expose] def spinRow : Native.Gen → ℕ → Terms
  | .rho q => monoRow (Native.ePauliN q)
  | .perm arr => monoRow (Native.ePermN arr)
  | .sign a => monoRow (Native.eYN a)
  | .xi => xiRow
  | .tau => fun _ => []

@[expose] def latRow : Native.Gen → ℕ → Terms
  | .rho _, j => [(j, 1)]
  | .perm arr, j => [(arr[j]!, 1)]
  | .sign a, j => [(j, Model.sgnI ((Model.wordN a).testBit j))]
  | .xi, j => (List.range 4).map fun m => (4 * (j / 4) + m, Model.c4N (j % 4) m / 32)
  | .tau, _ => []

@[expose] def rowE : Native.Gen → ℕ
  | .xi => 6
  | _ => 0

@[expose] def latE : Native.Gen → ℕ
  | .xi => 1
  | _ => 0

@[expose] def exW (g : Native.Gen) : ℕ := rowE g + latE g

@[expose] def colW (g : Native.Gen) (k : ℕ) : Terms :=
  (spinRow g (k / 24)).flatMap fun a => (latRow g (k % 24)).map fun c => (24 * a.1 + c.1, a.2 * c.2)

@[expose] def okW (g : Native.Gen) (k : ℕ) : Bool :=
  decide (k < 98304) && (latRow g (k % 24)).all fun c => decide (c.1 < 24)

@[expose] def isTau : Native.Gen → Bool
  | .tau => true
  | _ => false

theorem gdSpec_of (g : Native.Gen) (hg : isTau g = false) (hv : g.validB = true) :
    GDSpec (Native.GD.ofGen (Native.mkCtx ()) g) g.pair := by
  cases g with
  | rho q => exact gdSpec_rho q
  | perm arr => exact gdSpec_perm arr (permOf arr) (permOf_spec hv)
  | sign a => exact gdSpec_sign a
  | xi => exact gdSpec_xi
  | tau => simp [isTau] at hg

theorem rowT_eq (g : Native.Gen) (hg : isTau g = false) (r : ℕ) (hr : r < 4096) :
    (Native.GD.ofGen (Native.mkCtx ()) g).rowT[r]! = spinRow g r := by
  cases g with
  | rho q => exact monoRows_get _ r hr
  | perm arr =>
    rw [ofGen_perm]
    exact monoRows_get _ r hr
  | sign a => exact monoRows_get _ r hr
  | xi => exact xiRows_get r hr
  | tau => simp [isTau] at hg

theorem rowS_eq (g : Native.Gen) (hg : isTau g = false) :
    (Native.GD.ofGen (Native.mkCtx ()) g).rowS = rowE g := by
  cases g with
  | perm arr => rw [ofGen_perm]; rfl
  | tau => simp [isTau] at hg
  | _ => rfl

theorem latS_eq (g : Native.Gen) (hg : isTau g = false) :
    (Native.GD.ofGen (Native.mkCtx ()) g).latS = latE g := by
  cases g with
  | perm arr => rw [ofGen_perm]; rfl
  | tau => simp [isTau] at hg
  | _ => rfl

theorem xi_lat_entries : ∀ j : Fin 24, ∀ m : Fin 24,
    (if (j : ℕ) / 4 = (m : ℕ) / 4 then Model.c4N ((j : ℕ) % 4) ((m : ℕ) % 4) / 32 else 0) =
      (((List.range 4).map fun x => (4 * ((j : ℕ) / 4) + x, Model.c4N ((j : ℕ) % 4) x / 32)).map
        fun c => if c.1 = (m : ℕ) then c.2 else 0).sum := by
  decide +kernel

theorem ofGen_rho (q : Model.Pauli) :
    Native.GD.ofGen (Native.mkCtx ()) (.rho q) =
      ⟨0, Native.idG, Native.tabT (Native.conjPauliN q), Native.tabD (Native.conjPauliN q), 0,
        Native.monoRows (Native.ePauliN q)⟩ := rfl

theorem ofGen_sign (a : ℕ) :
    Native.GD.ofGen (Native.mkCtx ()) (.sign a) =
      ⟨0, Native.signG a, Native.tabT (Native.conjYN a), Native.tabD (Native.conjYN a), 0,
        Native.monoRows (Native.eYN a)⟩ := rfl

theorem ofGen_xi :
    Native.GD.ofGen (Native.mkCtx ()) .xi =
      ⟨1, Native.xiG, Native.tabT Native.conjXiN, Native.tabD Native.conjXiN, 6, Native.xiRows ()⟩ :=
  rfl

theorem G_eq (g : Native.Gen) (hg : isTau g = false) (j m : Fin 24) :
    (Native.GD.ofGen (Native.mkCtx ()) g).G.getD ((j : ℕ) * 24 + m) 0 =
      ((latRow g j).map fun c => if c.1 = (m : ℕ) then c.2 else 0).sum := by
  cases g with
  | rho q =>
    rw [ofGen_rho]
    dsimp only
    rw [idG_getD]
    simp [latRow, Fin.ext_iff]
  | perm arr =>
    rw [ofGen_perm]
    dsimp only
    rw [permG_getD]
    simp [latRow]
  | sign a =>
    rw [ofGen_sign]
    dsimp only
    rw [signG_getD]
    by_cases h : j = m
    · subst h
      simp [latRow]
    · have h' : ¬ (j : ℕ) = m := fun e => h (Fin.ext e)
      simp [latRow, h, h']
  | xi =>
    rw [ofGen_xi]
    dsimp only
    rw [xiG_getD]
    exact xi_lat_entries j m
  | tau => simp [isTau] at hg

@[expose] noncomputable def wB (k : ℕ) : SpaceW := tensor (eRow (k / 24)) (Pi.single (finOf (k % 24)) 1)

@[expose] noncomputable def semW (g : Native.Gen) : SpaceW →ₗ[ℚ] SpaceW :=
  thetaW (g.pair.1.1 : Matrix SpinIdx SpinIdx ℚ) (mat g.pair.1.2)

theorem wB_mk (a c : ℕ) (hc : c < 24) : wB (24 * a + c) = tensor (eRow a) (Pi.single (finOf c) 1) := by
  unfold wB
  rw [show (24 * a + c) / 24 = a by omega, show (24 * a + c) % 24 = c by omega]

theorem tensor_sum_right (q : SpinIdx → ℚ) (B : Terms) (hB : ∀ c ∈ B, c.1 < 24) (a : ℕ)
    (hq : q = eRow a) :
    tensor q ((B.map fun c => (c.2 : ℚ) • (Pi.single (finOf c.1) 1 : Fin 24 → ℚ)).sum) =
      sumT wB (B.map fun c => (24 * a + c.1, c.2)) := by
  induction B with
  | nil =>
    ext s m
    simp [tensor, vecMulVec_apply, sumT]
  | cons c B ih =>
    have h1 := ih fun c' hc' => hB c' (List.mem_cons_of_mem _ hc')
    simp only [List.map_cons, List.sum_cons, sumT_cons] at h1 ⊢
    rw [← h1, wB_mk a c.1 (hB c List.mem_cons_self), ← hq]
    unfold tensor
    rw [vecMulVec_add, vecMulVec_smul]

theorem tensor_sum (A B : Terms) (hB : ∀ c ∈ B, c.1 < 24) :
    tensor ((A.map fun a => (a.2 : ℚ) • eRow a.1).sum)
        ((B.map fun c => (c.2 : ℚ) • (Pi.single (finOf c.1) 1 : Fin 24 → ℚ)).sum) =
      sumT wB (A.flatMap fun a => B.map fun c => (24 * a.1 + c.1, a.2 * c.2)) := by
  induction A with
  | nil => simp [tensor]
  | cons a A ih =>
    simp only [List.map_cons, List.sum_cons, List.flatMap_cons, sumT_append]
    rw [← ih]
    unfold tensor
    rw [add_vecMulVec, smul_vecMulVec]
    congr 1
    have h2 := tensor_sum_right (eRow a.1) B hB a.1 rfl
    unfold tensor at h2
    rw [h2]
    have h3 : (B.map fun c => (24 * a.1 + c.1, a.2 * c.2)) =
        (B.map fun c => (24 * a.1 + c.1, c.2)).map fun u => (u.1, a.2 * u.2) := by
      simp
    rw [h3, sumT_map_mul]

theorem sum_single_apply (B : Terms) (hB : ∀ c ∈ B, c.1 < 24) (m : Fin 24) :
    ((B.map fun c => (c.2 : ℚ) • (Pi.single (finOf c.1) 1 : Fin 24 → ℚ)).sum) m =
      (((B.map fun c => if c.1 = (m : ℕ) then c.2 else 0).sum : ℤ) : ℚ) := by
  induction B with
  | nil => simp
  | cons c B ih =>
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, Int.cast_add,
      ih fun c' hc' => hB c' (List.mem_cons_of_mem _ hc')]
    congr 1
    have hc' := hB c List.mem_cons_self
    have hiff : m = finOf c.1 ↔ c.1 = (m : ℕ) := by
      constructor
      · intro h
        rw [h, finOf_val _ hc']
      · intro h
        apply Fin.ext
        rw [finOf_val _ hc', h]
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    by_cases h : c.1 = (m : ℕ)
    · rw [ite_eq_left (hiff.2 h), ite_eq_left h]
      simp
    · rw [ite_eq_right (fun e => h (hiff.1 e)), ite_eq_right h]
      simp

theorem semW_wB (g : Native.Gen) (hg : isTau g = false) (hv : g.validB = true) (k : ℕ)
    (hk : okW g k = true) : semW g (wB k) = ((1 : ℚ) / 2 ^ exW g) • sumT wB (colW g k) := by
  have hs := gdSpec_of g hg hv
  simp only [okW, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk
  obtain ⟨hk1, hk2⟩ := hk
  have hr : k / 24 < 4096 := by omega
  have hj : k % 24 < 24 := Nat.mod_lt _ (by norm_num)
  unfold wB semW
  rw [thetaW_tensor]
  have e1 : eRow (k / 24) = Pi.single (spinOfRow (k / 24)) 1 := by rw [eRow, ite_eq_left hr]
  rw [e1, hs.row _ hr, rowT_eq g hg _ hr, rowS_eq g hg]
  have e2 : (Pi.single (finOf (k % 24)) 1 : Fin 24 → ℚ) ᵥ* mat g.pair.1.2 =
      ((1 : ℚ) / 2 ^ latE g) •
        ((latRow g (k % 24)).map fun c => (c.2 : ℚ) • (Pi.single (finOf c.1) 1 : Fin 24 → ℚ)).sum := by
    funext m
    rw [single_one_vecMul, Matrix.row_apply, hs.lat, latS_eq g hg, G_eq g hg, finOf_val _ hj,
      Pi.smul_apply, sum_single_apply _ hk2 m, smul_eq_mul]
    ring
  rw [e2]
  have e3 : ((spinRow g (k / 24)).map fun t => ((t.2 : ℚ) / 2 ^ rowE g) • eRow t.1).sum =
      ((1 : ℚ) / 2 ^ rowE g) • ((spinRow g (k / 24)).map fun a => (a.2 : ℚ) • eRow a.1).sum := by
    rw [List.smul_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, smul_smul]
    ring_nf
  rw [e3]
  unfold tensor
  rw [smul_vecMulVec, vecMulVec_smul, smul_smul]
  have h4 := tensor_sum (spinRow g (k / 24)) (latRow g (k % 24)) hk2
  unfold tensor at h4
  rw [h4, exW, pow_add]
  congr 1
  field_simp

@[expose] noncomputable def vS (g : Native.Gen) : (SpinIdx → ℚ) →ₗ[ℚ] (SpinIdx → ℚ) :=
  Matrix.vecMulLinear (g.pair.1.1 : Matrix SpinIdx SpinIdx ℚ)

@[expose] noncomputable def vL (g : Native.Gen) : (Fin 24 → ℚ) →ₗ[ℚ] (Fin 24 → ℚ) :=
  Matrix.vecMulLinear (mat g.pair.1.2)

@[expose] noncomputable def eL (j : ℕ) : Fin 24 → ℚ := Pi.single (finOf j) 1

@[expose] def okS (_ : Native.Gen) (r : ℕ) : Bool := decide (r < 4096)

@[expose] def okL (g : Native.Gen) (j : ℕ) : Bool :=
  decide (j < 24) && (latRow g j).all fun c => decide (c.1 < 24)

theorem vS_eRow (g : Native.Gen) (hg : isTau g = false) (hv : g.validB = true) (r : ℕ)
    (hr : okS g r = true) : vS g (eRow r) = ((1 : ℚ) / 2 ^ rowE g) • sumT eRow (spinRow g r) := by
  have hs := gdSpec_of g hg hv
  have hr' : r < 4096 := by simpa [okS] using hr
  unfold vS
  rw [Matrix.vecMulLinear_apply]
  have e1 : eRow r = Pi.single (spinOfRow r) 1 := by rw [eRow, ite_eq_left hr']
  rw [e1, hs.row _ hr', rowT_eq g hg _ hr', rowS_eq g hg]
  unfold sumT
  rw [List.smul_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [Function.comp_apply, smul_smul]
  ring_nf

theorem vL_eL (g : Native.Gen) (hg : isTau g = false) (hv : g.validB = true) (j : ℕ)
    (hj : okL g j = true) : vL g (eL j) = ((1 : ℚ) / 2 ^ latE g) • sumT eL (latRow g j) := by
  have hs := gdSpec_of g hg hv
  simp only [okL, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hj
  obtain ⟨hj1, hj2⟩ := hj
  unfold vL eL
  rw [Matrix.vecMulLinear_apply]
  funext m
  rw [single_one_vecMul, Matrix.row_apply, hs.lat, latS_eq g hg, G_eq g hg, finOf_val _ hj1,
    Pi.smul_apply]
  unfold sumT
  rw [sum_single_apply _ hj2 m, smul_eq_mul]
  ring

theorem semW_tensor (g : Native.Gen) (x : SpinIdx → ℚ) (y : Fin 24 → ℚ) :
    semW g (tensor x y) = tensor (vS g x) (vL g y) := by
  unfold semW vS vL
  rw [thetaW_tensor, Matrix.vecMulLinear_apply, Matrix.vecMulLinear_apply]

@[expose] noncomputable def wordW (w : List Native.Gen) (N : SpaceW) : SpaceW :=
  w.foldl (fun x g => semW g x) N

theorem wordW_tensor : ∀ (w : List Native.Gen) (x : SpinIdx → ℚ) (y : Fin 24 → ℚ),
    wordW w (tensor x y) =
      tensor (w.foldl (fun x g => vS g x) x) (w.foldl (fun y g => vL g y) y)
  | [], _, _ => rfl
  | g :: w, x, y => by
    have := wordW_tensor w (vS g x) (vL g y)
    unfold wordW at this ⊢
    rw [List.foldl_cons, semW_tensor, this]
    rfl

@[expose] def WSupp (v : Native.DVec) : Prop :=
  v.D.size = 196884 ∧ ∀ k < 98580, v.D.getD k 0 = 0

theorem aIdx_lt : ∀ i < 24, ∀ j < 24, Native.aIdx i j < 300 := by decide +kernel

theorem latA_getD_zero (G D : Array ℤ) (hD : ∀ k < 98580, D.getD k 0 = 0) (z : ℕ) :
    (Native.latA G D).getD z 0 = 0 := by
  have hR : ∀ x, (Native.mmA (Native.trA G) (Native.mmA (Native.aFull D) G)).getD x 0 = 0 := by
    intro x
    by_cases hx : x < 576
    · have e : x = x / 24 * 24 + x % 24 := by omega
      rw [e, Native.latA_aIdx_aux _ _ _ _ (by omega) (Nat.mod_lt _ (by norm_num))]
      refine Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun l hl => ?_
      rw [hD _ (by have := aIdx_lt k (Finset.mem_range.1 hk) l (Finset.mem_range.1 hl); omega)]
      ring
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Native.mmA_size]; omega)]
      rfl
  by_cases hz : z < 300
  · unfold Native.latA
    rw [Native.getD_ofFn _ _ hz]
    simp only [Native.getElem!_eq_getD', hR]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [Native.latA_size]; omega)]
    rfl

theorem applyGD_WSupp (c : Native.Ctx) (g : Native.GD) (v : Native.DVec) (h : WSupp v) :
    WSupp (Native.applyGD c g v) := by
  obtain ⟨hs, hz⟩ := h
  refine ⟨?_, fun k hk => ?_⟩
  · change (Native.scale _ (Native.latA g.G v.D) ++ Native.scale _ (Native.scatterAt 300 98280 (g.xT c) v.D) ++
      Native.scale _ (Native.scatterAt 0 98304 g.wT (Native.wMul g.G v.D))).size = _
    simp only [Array.size_append, Native.scale_size, Native.latA_size, Native.scatterAt_size]
  · rw [Native.applyGD_getD]
    by_cases h1 : k < 300
    · rw [ite_eq_left h1, latA_getD_zero _ _ hz, zero_mul]
    · rw [ite_eq_right h1, ite_eq_left hk, Native.scatterAt_getD _ _ _ _ _ (by omega)]
      rw [Finset.sum_eq_zero fun p hp => ?_, zero_mul]
      rw [hz _ (by have := Finset.mem_range.1 hp; omega)]
      simp

theorem reduceN_WSupp : ∀ (n : ℕ) (v : Native.DVec), WSupp v → WSupp (Native.reduceN n v)
  | 0, _, h => h
  | n + 1, v, h => by
    unfold Native.reduceN
    split_ifs
    · refine reduceN_WSupp n _ ⟨?_, fun k hk => ?_⟩
      · simp [h.1]
      · change (v.D.map (· / 2)).getD k 0 = 0
        rw [getD_map_div2, h.2 k hk]
        rfl
    · exact h

theorem applyGen_of_not_tau (c : Native.Ctx) (g : Native.Gen) (hg : isTau g = false) (v : Native.DVec) :
    Native.applyGen c g v = Native.applyGD c (Native.GD.ofGen c g) v := by
  cases g with
  | tau => simp [isTau] at hg
  | _ => rfl

theorem evalWordC_WSupp (c : Native.Ctx) :
    ∀ (w : List Native.Gen), (∀ g ∈ w, isTau g = false) →
      ∀ v, WSupp v → WSupp (Native.evalWordC c w v)
  | [], _, _, h => h
  | g :: w, hw, v, h => by
    rw [evalWordC_cons]
    refine evalWordC_WSupp c w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')) _ ?_
    rw [applyGen_of_not_tau c g (hw g List.mem_cons_self)]
    exact reduceN_WSupp _ _ (applyGD_WSupp c _ v h)

theorem interpW_reduce (v : Native.DVec) : interpW v.reduce = interpW v := by
  ext s j
  change cf v.reduce _ = cf v _
  rw [Native.DVec.reduce, cf_reduceN]

theorem interpW_evalWordC :
    ∀ (w : List Native.Gen), (∀ g ∈ w, isTau g = false ∧ g.validB = true) →
      ∀ v, interpW (Native.evalWordC (Native.mkCtx ()) w v) = wordW w (interpW v)
  | [], _, _ => rfl
  | g :: w, hw, v => by
    have hg := hw g List.mem_cons_self
    rw [evalWordC_cons, interpW_evalWordC w (fun g' hg' => hw g' (List.mem_cons_of_mem _ hg')),
      interpW_reduce, applyGen_of_not_tau _ g hg.1,
      interpW_applyGD _ _ (gdSpec_of g hg.1 hg.2)]
    rfl

theorem interpW_single (K : ℕ) (hK : K < 98304) :
    interpW (Native.DVec.ofList [(98580 + K, 1)]) = wB K := by
  ext s m
  have hr := rowOf_lt s
  simp only [interpW, of_apply]
  rw [CFSG.Monster.Existence.Census.ofList_single_getD _ _ (by omega)]
  have he : (Native.DVec.ofList [(98580 + K, 1)]).e = 0 := rfl
  rw [he, pow_zero, div_one]
  unfold wB tensor
  rw [vecMulVec_apply, eRow_apply, Pi.single_apply]
  have hm := m.2
  have hiff : 98580 + 24 * rowOf s + (m : ℕ) = 98580 + K ↔
      (K / 24 < 4096 ∧ K / 24 = rowOf s) ∧ m = finOf (K % 24) := by
    constructor
    · intro h
      refine ⟨⟨by omega, by omega⟩, Fin.ext ?_⟩
      rw [finOf_val _ (Nat.mod_lt _ (by norm_num))]
      omega
    · rintro ⟨⟨-, h1⟩, h2⟩
      have := congrArg Fin.val h2
      rw [finOf_val _ (Nat.mod_lt _ (by norm_num))] at this
      omega
  by_cases h : 98580 + 24 * rowOf s + (m : ℕ) = 98580 + K
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h).1, ite_eq_left (hiff.1 h).2]
    simp
  · rw [ite_eq_right h]
    by_cases h1 : K / 24 < 4096 ∧ K / 24 = rowOf s
    · rw [ite_eq_left h1, ite_eq_right (fun e => h (hiff.2 ⟨h1, e⟩))]
      simp
    · rw [ite_eq_right h1]
      simp

theorem WSupp_single (K : ℕ) (hK : K < 98304) : WSupp (Native.DVec.ofList [(98580 + K, 1)]) := by
  refine ⟨?_, fun k hk => ?_⟩
  · simp [Native.DVec.ofList, Native.DVec.ofListE, show 98580 + K < 196884 by omega]
  · rw [CFSG.Monster.Existence.Census.ofList_single_getD _ _ (by omega), ite_eq_right (by omega)]

theorem eqv_of_interpW {v w : Native.DVec} (hv : WSupp v) (hw : WSupp w)
    (h : interpW v = interpW w) : v.eqv w = true := by
  unfold Native.DVec.eqv
  rw [beq_iff_eq]
  have key : ∀ k < 196884, (Native.scale (max v.e w.e - v.e) v.D).getD k 0 =
      (Native.scale (max v.e w.e - w.e) w.D).getD k 0 := by
    intro k hk
    rw [Native.scale_getD _ _ _ (by rw [hv.1]; exact hk), Native.scale_getD _ _ _ (by rw [hw.1]; exact hk)]
    by_cases h1 : k < 98580
    · rw [hv.2 k h1, hw.2 k h1, zero_mul, zero_mul]
    · have hr : (k - 98580) / 24 < 4096 := by omega
      have hj : (k - 98580) % 24 < 24 := Nat.mod_lt _ (by norm_num)
      have he := congrFun (congrFun h (spinOfRow ((k - 98580) / 24))) (finOf ((k - 98580) % 24))
      simp only [interpW, of_apply, rowOf_spinOfRow hr, finOf_val _ hj] at he
      rw [show 98580 + 24 * ((k - 98580) / 24) + (k - 98580) % 24 = k by omega] at he
      have h2 : ((v.D.getD k 0 * 2 ^ (max v.e w.e - v.e) : ℤ) : ℚ) =
          ((w.D.getD k 0 * 2 ^ (max v.e w.e - w.e) : ℤ) : ℚ) := by
        push_cast
        have p1 : (2 : ℚ) ^ (max v.e w.e - v.e) = 2 ^ max v.e w.e / 2 ^ v.e := by
          rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
        have p2 : (2 : ℚ) ^ (max v.e w.e - w.e) = 2 ^ max v.e w.e / 2 ^ w.e := by
          rw [eq_div_iff (by positivity), ← pow_add, Nat.sub_add_cancel (le_max_right _ _)]
        rw [p1, p2, mul_div_assoc', mul_div_assoc', mul_comm, mul_div_assoc, he, ← mul_div_assoc,
          mul_comm]
      exact_mod_cast h2
  apply Array.ext
  · rw [Native.scale_size, Native.scale_size, hv.1, hw.1]
  · intro i h1 h2
    have hi : i < 196884 := by rw [Native.scale_size, hv.1] at h1; exact h1
    have := key i hi
    rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

@[expose] def keyW (k : Bool × ℕ × Fin 24) : ℕ := 24 * Native.rowIdx k.1 k.2.1 + k.2.2

@[expose] def pairOK : Bool × ℕ × Terms → Bool × ℕ × Terms → Bool
  | (f₁, e₁, l₁), (f₂, e₂, l₂) => f₁ && f₂ && eqST e₁ l₁ e₂ l₂

@[expose] def latEq (w₁ w₂ : List Native.Gen) (neg : Bool) (j : ℕ) : Bool :=
  match runT okL latRow latE w₁ (true, 0, [(j, 1)]), runT okL latRow latE w₂ (true, 0, [(j, 1)]) with
  | (f₁, d₁, L₁), (f₂, d₂, L₂) => f₁ && f₂ && eqST d₁ L₁ d₂ (cond neg (negT L₂) L₂)

@[expose] def groupOK (w₁ w₂ : List Native.Gen) (s : ℕ) (js : List ℕ) : Bool :=
  match runT okS spinRow rowE w₁ (true, 0, [(s, 1)]), runT okS spinRow rowE w₂ (true, 0, [(s, 1)]) with
  | (f₁, e₁, S₁), (f₂, e₂, S₂) =>
    f₁ && f₂ && cond (eqST e₁ S₁ e₂ S₂) (js.all (latEq w₁ w₂ false))
      (eqST e₁ S₁ e₂ (negT S₂) && js.all (latEq w₁ w₂ true))

@[expose] def rigidGroups : List (ℕ × List ℕ) :=
  (Native.rowIdx false 0, List.range 24) ::
    CFSG.Monster.Existence.Census.rigidRows.map fun x => (Native.rowIdx x.1 x.2, [0])

@[expose] def checkW (w₁ w₂ : List Native.Gen) : Bool :=
  (w₁ ++ w₂).all (fun g => g.validB) && (w₁ ++ w₂).all (fun g => !isTau g) &&
    rigidGroups.all fun G => groupOK w₁ w₂ G.1 G.2

theorem rigidGroups_cover (k : Bool × ℕ × Fin 24) (hk : k ∈ CFSG.Monster.Existence.Census.rigidKeys) :
    ∃ G ∈ rigidGroups, G.1 = Native.rowIdx k.1 k.2.1 ∧ (k.2.2 : ℕ) ∈ G.2 := by
  unfold CFSG.Monster.Existence.Census.rigidKeys at hk
  rcases List.mem_append.1 hk with h | h
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 h
    exact ⟨_, List.mem_cons_self, rfl, List.mem_range.2 j.2⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩), rfl, List.mem_singleton_self _⟩

theorem foldl_start {M : Type*} [AddCommGroup M] [Module ℚ M] (b : ℕ → M) (f : Native.Gen → M →ₗ[ℚ] M)
    (w : List Native.Gen) (s : ℕ) :
    w.foldl (fun x g => f g x) (b s) = w.foldl (fun x g => f g x) (((1 : ℚ) / 2 ^ 0) • sumT b [(s, 1)]) := by
  simp [sumT]

theorem groupOK_sound {w₁ w₂ : List Native.Gen} (hw₁ : ∀ g ∈ w₁, isTau g = false ∧ g.validB = true)
    (hw₂ : ∀ g ∈ w₂, isTau g = false ∧ g.validB = true) {s : ℕ} {js : List ℕ}
    (h : groupOK w₁ w₂ s js = true) :
    ∀ j ∈ js, wordW w₁ (tensor (eRow s) (eL j)) = wordW w₂ (tensor (eRow s) (eL j)) := by
  have sS : ∀ w : List Native.Gen, (∀ g ∈ w, isTau g = false ∧ g.validB = true) →
      ∀ g ∈ w, ∀ r, okS g r = true → vS g (eRow r) = ((1 : ℚ) / 2 ^ rowE g) • sumT eRow (spinRow g r) :=
    fun w hw g hg r hr => vS_eRow g (hw g hg).1 (hw g hg).2 r hr
  have sL : ∀ w : List Native.Gen, (∀ g ∈ w, isTau g = false ∧ g.validB = true) →
      ∀ g ∈ w, ∀ j, okL g j = true → vL g (eL j) = ((1 : ℚ) / 2 ^ latE g) • sumT eL (latRow g j) :=
    fun w hw g hg j hj => vL_eL g (hw g hg).1 (hw g hg).2 j hj
  unfold groupOK at h
  generalize e1 : runT okS spinRow rowE w₁ (true, 0, [(s, 1)]) = r₁ at h
  generalize e2 : runT okS spinRow rowE w₂ (true, 0, [(s, 1)]) = r₂ at h
  obtain ⟨f₁, x₁, S₁⟩ := r₁
  obtain ⟨f₂, x₂, S₂⟩ := r₂
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hf1, hf2⟩, hc⟩ := h
  have p1 := runT_sound eRow vS okS spinRow rowE w₁ (sS w₁ hw₁) 0 [(s, 1)] (by rw [e1]; exact hf1)
  have p2 := runT_sound eRow vS okS spinRow rowE w₂ (sS w₂ hw₂) 0 [(s, 1)] (by rw [e2]; exact hf2)
  rw [e1] at p1
  rw [e2] at p2
  rw [← foldl_start] at p1 p2
  intro j hj
  rw [wordW_tensor, wordW_tensor, p1, p2]
  have lat : ∀ neg, latEq w₁ w₂ neg j = true →
      w₁.foldl (fun y g => vL g y) (eL j) =
        cond neg (-w₂.foldl (fun y g => vL g y) (eL j)) (w₂.foldl (fun y g => vL g y) (eL j)) := by
    intro neg hl
    unfold latEq at hl
    generalize e3 : runT okL latRow latE w₁ (true, 0, [(j, 1)]) = t₁ at hl
    generalize e4 : runT okL latRow latE w₂ (true, 0, [(j, 1)]) = t₂ at hl
    obtain ⟨g₁, y₁, L₁⟩ := t₁
    obtain ⟨g₂, y₂, L₂⟩ := t₂
    simp only [Bool.and_eq_true] at hl
    obtain ⟨⟨hg1, hg2⟩, he⟩ := hl
    have q1 := runT_sound eL vL okL latRow latE w₁ (sL w₁ hw₁) 0 [(j, 1)] (by rw [e3]; exact hg1)
    have q2 := runT_sound eL vL okL latRow latE w₂ (sL w₂ hw₂) 0 [(j, 1)] (by rw [e4]; exact hg2)
    rw [e3] at q1
    rw [e4] at q2
    rw [← foldl_start] at q1 q2
    rw [q1, q2]
    have := smul_sumT_eq_of_eqT eL he
    cases neg
    · exact this
    · rw [this, Bool.cond_true, Bool.cond_true, sumT_negT, smul_neg]
  cases hS : eqST x₁ S₁ x₂ S₂
  · rw [hS] at hc
    simp only [Bool.cond_false, Bool.and_eq_true] at hc
    have hy := lat true (List.all_eq_true.1 hc.2 j hj)
    have hx := smul_sumT_eq_of_eqT eRow hc.1
    rw [sumT_negT, smul_neg] at hx
    rw [hx, hy]
    unfold tensor
    simp [neg_vecMulVec, vecMulVec_neg]
  · rw [hS] at hc
    simp only [Bool.cond_true] at hc
    have hy := lat false (List.all_eq_true.1 hc j hj)
    rw [smul_sumT_eq_of_eqT eRow hS, hy]
    rfl

theorem keyW_lt (k : Bool × ℕ × Fin 24) : keyW k < 98304 := by
  have := CFSG.Monster.Existence.Census.rowIdx_lt k.1 k.2.1
  have := k.2.2.2
  unfold keyW
  omega

theorem checkRigid_of_checkW {w₁ w₂ : List Native.Gen} (h : checkW w₁ w₂ = true) :
    CFSG.Monster.Existence.Census.checkRigid (Native.mkCtx ()) w₁ w₂ = true := by
  simp only [checkW, Bool.and_eq_true] at h
  obtain ⟨⟨hv, ht⟩, hr⟩ := h
  have hg : ∀ g ∈ w₁ ++ w₂, isTau g = false ∧ g.validB = true := fun g hg =>
    ⟨by simpa using List.all_eq_true.1 ht g hg, List.all_eq_true.1 hv g hg⟩
  have hg1 : ∀ g ∈ w₁, isTau g = false ∧ g.validB = true := fun g h => hg g (List.mem_append_left _ h)
  have hg2 : ∀ g ∈ w₂, isTau g = false ∧ g.validB = true := fun g h => hg g (List.mem_append_right _ h)
  unfold CFSG.Monster.Existence.Census.checkRigid
  rw [hv, Bool.true_and]
  refine List.all_eq_true.2 fun k hk => ?_
  have hrd : CFSG.Monster.Existence.Census.rigidDVec k = Native.DVec.ofList [(98580 + keyW k, 1)] := by
    unfold CFSG.Monster.Existence.Census.rigidDVec keyW
    rw [Nat.add_assoc]
  rw [hrd]
  have hs := WSupp_single _ (keyW_lt k)
  refine eqv_of_interpW (evalWordC_WSupp _ w₁ (fun g h => (hg1 g h).1) _ hs)
    (evalWordC_WSupp _ w₂ (fun g h => (hg2 g h).1) _ hs) ?_
  rw [interpW_evalWordC w₁ hg1, interpW_evalWordC w₂ hg2, interpW_single _ (keyW_lt k)]
  obtain ⟨G, hG, h1, h2⟩ := rigidGroups_cover k hk
  have hgk := groupOK_sound hg1 hg2 (List.all_eq_true.1 hr G hG) _ h2
  rw [h1] at hgk
  unfold keyW
  rw [wB_mk _ _ k.2.2.2]
  exact hgk

end CertificateChecks.MonsterExist.RigidW
