module

public import Certificates.Kernel.Sporadic.Co1Row26683.ChecksM
public import Certificates.Kernel.Sporadic.Co1Row26683.VecM
public import Certificates.Kernel.Sporadic.Co1Row26683.GlueZ
public import Certificates.Kernel.Co1B.C2043
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.SporSch.Co1HeisSound
public import CFSG.Certificates.Kernel.SporSch.Co1ActLemmas
public import CFSG.Certificates.Kernel.SporSch.Co1SplitSound
public import CFSG.Sporadic.Co1Block.Classes
public import CFSG.Sporadic.Co1Block.XFix
public import CFSG.Sporadic.Co1Block.TwoBComp
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Enum.ZCSound
public import CFSG.Sporadic.Co1.Module.InvAssemble

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.SporSch.M24
  CFSG.KS.Co1Row26683M CertificateChecks.KernelCo1B CertificateChecks.KernelCo1B.Tri2045
  CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.Co1Packed

theorem encW_eq (w : List Int) : encW w = encWordK w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    change CFSG.KS.Mathieu.icode z :: encW w = encLetterK z :: encWordK w
    rw [ih]
    rfl

theorem encWL_dec (ws : List (List Int)) : (encWL ws).map Native.decWord = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change Native.decWord (encW w) :: (encWL ws).map Native.decWord = w :: ws
    rw [ih, encW_eq, decWord_encWordK]

theorem rep_mW {X Y : Nat} {g h : GL24} (hX : MRep (unpack 24 24 X) g)
    (hY : MRep (unpack 24 24 Y) h) : MRep (unpack 24 24 (mW X Y)) (g * h) := by
  have := hX.mul hY
  rwa [mul_unpackW] at this

theorem rep_idM : MRep (unpack 24 24 idM) 1 := by
  rw [MatL.unpack_idM]
  exact MRep.one

theorem dag_reps {M MI : Nat → Nat} {nb N : Nat} {ws : List (List Int)} {baseG : List GL24}
    (hb : List.Forall₂ MRep ((List.range nb).map fun i => unpack 24 24 (M i)) baseG)
    (h : dagWK M MI nb N (encWL ws) = true) {i : Nat} (hi : i < N) :
    MRep (unpack 24 24 (M i)) ((dagG baseG ws).getD i 1) ∧
      MRep (unpack 24 24 (MI i)) ((dagG baseG ws).getD i 1)⁻¹ := by
  have e := dagWK_sound rfl h
  rw [encWL_dec] at e
  have hd := dag_rep hb ws (by rw [e])
  rw [e] at hd
  have h1 := getD_rep hd MRep.one i
  rw [getD_range_unpack hi] at h1
  exact ⟨h1, h1.inv (invOKW_sound (dagWK_inv h i hi)).1⟩

theorem prodIdx_rep {M : Nat → Nat} {gs : List GL24} {H : Subgroup GL24}
    (hM : ∀ i < 12, MRep (unpack 24 24 (M i)) (gs.getD i 1)) (hH : ∀ i < 12, gs.getD i 1 ∈ H) :
    ∀ (w : List Nat) (acc : Nat) (g : GL24), allLtK 12 w = true → MRep (unpack 24 24 acc) g →
      ∃ h ∈ H, MRep (unpack 24 24 (List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
        (fun i _ ih acc => CFSG.KC.Enum.strictN (mW acc (M i)) ih) w acc)) (g * h)
  | [], _, _, _, hacc => ⟨1, H.one_mem, by rw [mul_one]; exact hacc⟩
  | i :: w, acc, g, hw, hacc => by
    obtain ⟨hi, hw⟩ := CFSG.KC.Pack.band_iff.1 hw
    have hi' : i < 12 := by simpa using hi
    obtain ⟨h, hh, hr⟩ := prodIdx_rep hM hH w _ _ hw (rep_mW hacc (hM i hi'))
    refine ⟨gs.getD i 1 * h, H.mul_mem (hH i hi') hh, ?_⟩
    change MRep (unpack 24 24 (CFSG.KC.Enum.strictN (mW acc (M i)) _)) _
    rw [CFSG.KC.Pack.strictN_eq, ← mul_assoc]
    exact hr

theorem matK_sound {X Y P₁ P₂ : Nat} {ZM ZMI LM LMI HM HMI : Nat → Nat} {wZ wL : List Int}
    {wH : List (List Int)} {W1 W2 : List Nat} {v : Nat}
    (h : matK X Y P₁ P₂ ZM ZMI LM LMI HM HMI wZ wL wH W1 W2 v = true) :
    mW X X = idM ∧ mW (mW (mW (mW Y Y) Y) Y) Y = idM ∧ ZM 0 = Y ∧ ZM 1 = mW (mW X Y) X ∧
      dagWK ZM ZMI 2 3 (encWL [wZ]) = true ∧ mW (ZM 2) (ZM 2) = idM ∧
      Bool.not (Nat.beq (ZM 2) idM) = true ∧ LM 0 = P₁ ∧ LM 1 = P₂ ∧
      dagWK LM LMI 2 3 (encWL [wL]) = true ∧ CFSG.KS.Co1Row26683M.conjK (LM 2) P₁ (LMI 2) = mW P₁ (ZM 2) ∧
      HM 0 = Y ∧ HM 1 = mW (mW X Y) X ∧ HM 2 = CFSG.KS.Co1Row26683M.conjK (LM 2) Y (LMI 2) ∧
      HM 3 = CFSG.KS.Co1Row26683M.conjK (LM 2) (mW (mW X Y) X) (LMI 2) ∧ dagWK HM HMI 4 12 (encWL wH) = true ∧
      allLtK 12 W1 = true ∧ allLtK 12 W2 = true ∧ prodIdxK HM W1 = P₁ ∧ prodIdxK HM W2 = P₂ ∧
      actK (ZM 2) v = v := by
  unfold matK at h
  rw [CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq, CFSG.KC.Pack.strictB_eq,
    CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h2, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h3, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h4, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h5, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h6, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h7, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h8, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h9, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h10, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h11, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h12, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h13, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h14, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h15, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h16, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h17, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h18, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h19, h⟩ := CFSG.KC.Pack.band_iff.1 h
  obtain ⟨h20, h21⟩ := CFSG.KC.Pack.band_iff.1 h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, h5, Nat.eq_of_beq_eq_true h6, h7, Nat.eq_of_beq_eq_true h8,
    Nat.eq_of_beq_eq_true h9, h10, Nat.eq_of_beq_eq_true h11, Nat.eq_of_beq_eq_true h12,
    Nat.eq_of_beq_eq_true h13, Nat.eq_of_beq_eq_true h14, Nat.eq_of_beq_eq_true h15, h16, h17,
    h18, Nat.eq_of_beq_eq_true h19, Nat.eq_of_beq_eq_true h20, Nat.eq_of_beq_eq_true h21⟩

theorem vec_parts {k v : Nat}
    (h : Bool.rec (motive := fun _ => Bool) false (Nat.beq (CFSG.KC.Co1B.vAt CV.F k) v)
      (Nat.blt k (nat_lit 98280)) = true) : k < 98280 ∧ CFSG.KC.Co1B.vAt CV.F k = v := by
  obtain ⟨h1, h2⟩ := CFSG.KC.Pack.band_iff.1 h
  exact ⟨CFSG.KC.Co1T.lt_of_blt h1, Nat.eq_of_beq_eq_true h2⟩

theorem kZs : Nat.beq (Nat.shiftRight (C26683M.Z.M (nat_lit 2)) (nat_lit 576)) (nat_lit 0) = true := by
  quickRfl

abbrev xM : GL24 := ((d₂C twoBXY.1 : GA) : GL24)

abbrev yM : GL24 := ((d₂C twoBXY.2 : GA) : GL24)

abbrev bM : GL24 := xM * yM * xM

theorem rep_xM : MRep (unpack 24 24 (Cent2045.D2.M 19)) xM := by
  have h : MRep twoBXYRows.1 xM := rep_d₂C twoBXY.1
  rwa [rx_eq] at h

theorem rep_yM : MRep (unpack 24 24 (Cent2045.D2.M 21)) yM := by
  have h : MRep twoBXYRows.2 yM := rep_d₂C twoBXY.2
  rwa [ry_eq] at h

theorem rep_P₁ : MRep (unpack 24 24 (Cent2045.D1.M 0)) A₁ := by
  rw [Nat.eq_of_beq_eq_true Cent2045.kb0]
  exact repA

theorem rep_P₂ : MRep (unpack 24 24 (Cent2045.D1.M 1)) A₂ := by
  rw [Nat.eq_of_beq_eq_true Cent2045.kb1, ← bR_u]
  exact rep_A₂

theorem xM_sq : xM * xM = 1 := by
  have h := rep_mW rep_xM rep_xM
  rw [(matK_sound ch26683M).1] at h
  exact h.eq rep_idM

theorem yM_pow : yM ^ 5 = 1 := by
  have h := rep_mW (rep_mW (rep_mW (rep_mW rep_yM rep_yM) rep_yM) rep_yM) rep_yM
  rw [(matK_sound ch26683M).2.1] at h
  rw [pow_succ, pow_succ, pow_succ, pow_succ, pow_one]
  exact h.eq rep_idM

theorem yM_mem : yM ∈ GA ⊓ Subgroup.centralizer {A₁} := coe_mem_C₁ (d₂C twoBXY.2)

theorem bM_mem : bM ∈ GA ⊓ Subgroup.centralizer {A₁} :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (coe_mem_C₁ (d₂C twoBXY.1)) yM_mem)
    (coe_mem_C₁ (d₂C twoBXY.1))

abbrev zM : GL24 := (dagG [yM, bM] [CFSG.EvenSporadicStandard.Solomon78.co1WordZ]).getD 2 1

abbrev lM : GL24 := (dagG [A₁, A₂] [CFSG.EvenSporadicStandard.Solomon78.co1WordL]).getD 2 1

theorem rep_bM : MRep (unpack 24 24 (mW (mW (Cent2045.D2.M 19) (Cent2045.D2.M 21))
    (Cent2045.D2.M 19))) bM := rep_mW (rep_mW rep_xM rep_yM) rep_xM

theorem rep_zM : MRep (unpack 24 24 (C26683M.Z.M 2)) zM := by
  obtain ⟨-, -, h3, h4, h5, -⟩ := (matK_sound ch26683M)
  refine (dag_reps ?_ h5 (by norm_num : 2 < 3)).1
  change List.Forall₂ MRep [unpack 24 24 (C26683M.Z.M 0), unpack 24 24 (C26683M.Z.M 1)] _
  rw [h3, h4]
  exact .cons rep_yM (.cons rep_bM .nil)

theorem rep_lM : MRep (unpack 24 24 (C26683M.L.M 2)) lM ∧
    MRep (unpack 24 24 (C26683M.L.MI 2)) lM⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, h8, h9, h10, -⟩ := (matK_sound ch26683M)
  refine dag_reps ?_ h10 (by norm_num : 2 < 3)
  change List.Forall₂ MRep [unpack 24 24 (C26683M.L.M 0), unpack 24 24 (C26683M.L.M 1)] _
  rw [h8, h9]
  exact .cons rep_P₁ (.cons rep_P₂ .nil)

theorem zM_closure : zM ∈ Subgroup.closure {yM, bM} := by
  refine getD_mem_of_forall (dagG_mem (fun g hg => Subgroup.subset_closure ?_) _) 2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem zM_mem : zM ∈ GA ⊓ Subgroup.centralizer {A₁} := by
  have hle : Subgroup.closure {yM, bM} ≤ GA ⊓ Subgroup.centralizer {A₁} := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact yM_mem
    · exact bM_mem
  exact hle zM_closure

theorem zM_sq : zM * zM = 1 := by
  have h := rep_mW rep_zM rep_zM
  rw [(matK_sound ch26683M).2.2.2.2.2.1] at h
  exact h.eq rep_idM

theorem zM_ne : zM ≠ 1 := by
  intro e
  have h7 := (matK_sound ch26683M).2.2.2.2.2.2.1
  have hne : Bool.rec (motive := fun _ => Bool) true false (Nat.beq (C26683M.Z.M 2) idM) =
      true := by
    revert h7
    cases Nat.beq (C26683M.Z.M 2) idM <;> simp
  have h1 := unpack_ne_one kZs hne
  have h2 := rep_zM
  rw [e] at h2
  have h3 := CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
    (by rw [← unpackR_eq_unpack]; exact CFSG.KC.Co1F2.validRows_unpackR _) validRows_one
    (h2.trans MRep.one.symm)
  rw [h3] at h1
  exact absurd h1 (by simp)

theorem lM_mem : lM ∈ GA := by
  have h : ∀ g ∈ [A₁, A₂], g ∈ GA := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h
    · rw [h]
      exact A₁_mem
    · rw [h]
      exact A₂_mem
  exact getD_mem_of_forall (dagG_mem h [CFSG.EvenSporadicStandard.Solomon78.co1WordL]) 2

theorem lM_conj : lM * A₁ * lM⁻¹ = A₁ * zM := by
  have h11 := (matK_sound ch26683M).2.2.2.2.2.2.2.2.2.2.1
  have e1 := rep_mW (rep_mW rep_lM.1 rep_P₁) rep_lM.2
  have e2 := rep_mW rep_P₁ rep_zM
  unfold CFSG.KS.Co1Row26683M.conjK at h11
  rw [h11] at e1
  exact e1.eq e2

theorem gen_le : GA ≤ Subgroup.closure {yM, bM, lM * yM * lM⁻¹, lM * bM * lM⁻¹} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13, h14, h15, h16, h17, h18, h19, h20, -⟩ :=
    (matK_sound ch26683M)
  set H := Subgroup.closure {yM, bM, lM * yM * lM⁻¹, lM * bM * lM⁻¹} with hH
  have hb : List.Forall₂ MRep ((List.range 4).map fun i => unpack 24 24 (C26683M.H.M i))
      [yM, bM, lM * yM * lM⁻¹, lM * bM * lM⁻¹] := by
    change List.Forall₂ MRep [unpack 24 24 (C26683M.H.M 0), unpack 24 24 (C26683M.H.M 1),
      unpack 24 24 (C26683M.H.M 2), unpack 24 24 (C26683M.H.M 3)] _
    rw [h12, h13, h14, h15]
    unfold CFSG.KS.Co1Row26683M.conjK
    exact .cons rep_yM (.cons rep_bM (.cons (rep_mW (rep_mW rep_lM.1 rep_yM) rep_lM.2)
      (.cons (rep_mW (rep_mW rep_lM.1 rep_bM) rep_lM.2) .nil)))
  have hM : ∀ i < 12, MRep (unpack 24 24 (C26683M.H.M i))
      ((dagG [yM, bM, lM * yM * lM⁻¹, lM * bM * lM⁻¹]
        CFSG.EvenSporadicStandard.Solomon78.co1DagH).getD i 1) := fun i hi =>
    (dag_reps hb h16 hi).1
  have hbase : ∀ g ∈ [yM, bM, lM * yM * lM⁻¹, lM * bM * lM⁻¹], g ∈ H := by
    intro g hg
    rw [hH]
    apply Subgroup.subset_closure
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h | h | h
    · rw [h]
      exact Set.mem_insert _ _
    · rw [h]
      exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [h]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · rw [h]
      exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hHm : ∀ i < 12, (dagG [yM, bM, lM * yM * lM⁻¹, lM * bM * lM⁻¹]
      CFSG.EvenSporadicStandard.Solomon78.co1DagH).getD i 1 ∈ H := fun i _ =>
    getD_mem_of_forall (dagG_mem hbase CFSG.EvenSporadicStandard.Solomon78.co1DagH) i
  have hA : ∀ {P : Nat} {a : GL24} (W : List Nat), allLtK 12 W = true →
      prodIdxK C26683M.H.M W = P → MRep (unpack 24 24 P) a → a ∈ H := by
    intro P a W hW hP ha
    obtain ⟨h, hh, hr⟩ := prodIdx_rep hM hHm W idM 1 hW rep_idM
    have hr' : MRep (unpack 24 24 (prodIdxK C26683M.H.M W)) (1 * h) := hr
    rw [hP, one_mul] at hr'
    rw [ha.eq hr']
    exact hh
  have h1 : A₁ ∈ H := hA _ h17 h19 rep_P₁
  have h2 : A₂ ∈ H := hA _ h18 h20 rep_P₂
  rw [GA_eq, Subgroup.closure_le]
  intro g hg
  rcases hg with h | h
  · rw [h]
    exact h1
  · rw [Set.mem_singleton_iff.1 h]
    exact h2

theorem zM_act {v : Nat} (e : actK (C26683M.Z.M 2) v = v) :
    Matrix.mulVec (zM : Matrix (Fin 24) (Fin 24) (ZMod 2)) (CFSG.Sporadic.SmallF2.toVecD 24 v) =
      CFSG.Sporadic.SmallF2.toVecD 24 v := by
  rw [MRep.mulVec rep_zM]
  exact congrArg (CFSG.Sporadic.SmallF2.toVecD 24)
    ((CFSG.KS.SporSch.M24.ActL.vecMulN_unpack _ _).trans e)

theorem zM_fix : ∃ w, w ∈ xFix zM := by
  have e := (matK_sound ch26683M).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hv := ch26683V
  generalize CFSG.KS.Mathieu.nget C26683M.ZV (nat_lit 1) = v at e hv
  generalize CFSG.KS.Mathieu.nget C26683M.ZV (nat_lit 0) = k at hv
  obtain ⟨hk', hvk⟩ := vec_parts hv
  have hvk' := hvk.symm.trans (vAt_eq hk')
  refine ⟨certVec k, ⟨k, hk', rfl⟩, ?_⟩
  rw [certVec, ← hvk']
  exact zM_act e

theorem zM_not_conj : ∀ x ∈ GA, x * A₁ * x⁻¹ ≠ zM := by
  obtain ⟨w, hfix⟩ := zM_fix
  intro x hx he
  have h1 := ncard_fix_conj (g := x) (s := A₁) hx
  rw [he] at h1
  have h0 : (xFix A₁).ncard = 0 := by
    have := ncard_fix_a₁
    rwa [coe_a₁] at this
  rw [h0, Set.ncard_eq_zero] at h1
  rw [h1] at hfix
  exact hfix

end CertificateChecks.KernelSpor.Co1Row26683

end
