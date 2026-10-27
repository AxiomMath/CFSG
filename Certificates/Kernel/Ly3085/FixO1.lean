
module

public import Certificates.Kernel.Ly3085.StabFix
public import Certificates.Kernel.Ly3085.Omega.O1FixK
public import CFSG.Certificates.Kernel.Common.GridChunks
public import Certificates.Kernel.Ly3085.FactsBase
public import Certificates.Kernel.Ly3085.O1Count
public import Certificates.Kernel.Ly3085.SimpleBase

public section

open CFSG.KC.LyOm CFSG.KD.LyO1 in
#kc_grid_chunks CFSG.KD.LyO1.FixTA blk all 1 306 CFSG.KD.LyO1.o1fTA [CT]
  (fun q => Nat.beq (cFix BC KX PT TA n q 1) (CT q) = true)
open CFSG.KC.LyOm CFSG.KD.LyO1 in
#kc_grid_chunks CFSG.KD.LyO1.FixTB blk all 1 306 CFSG.KD.LyO1.o1fTB [CT]
  (fun q => Nat.beq (cFix BC KX PT TB n q 1) (CT q) = true)
open CFSG.KC.LyOm CFSG.KD.LyO1 in
#kc_grid_chunks CFSG.KD.LyO1.FixTT blk all 1 306 CFSG.KD.LyO1.o1fTT [CT]
  (fun q => Nat.beq (cFix BC KX PT TT n q 1) (CT q) = true)
open CFSG.KC.LyOm CFSG.KD.LyO1 in
#kc_grid_chunks CFSG.KD.LyO1.FixYB blk all 1 306 CFSG.KD.LyO1.o1fYB [CT]
  (fun q => Nat.beq (cFix BC KX PT YB n q 1) (CT q) = true)

namespace CFSG.KD.LyO1

open CFSG.KC.Loop

theorem sumTA : Nat.beq (sumBelow 306 5 FixTA.CT) 155 = true := by decide +kernel
theorem sumTB : Nat.beq (sumBelow 306 5 FixTB.CT) 5 = true := by decide +kernel
theorem sumTT : Nat.beq (sumBelow 306 5 FixTT.CT) 66 = true := by decide +kernel
theorem sumYB : Nat.beq (sumBelow 306 5 FixYB.CT) 0 = true := by decide +kernel

end CFSG.KD.LyO1

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL CFSG.KC.Loop
open Matrix MulAction

theorem sameSpanL_complete {N Y : ℕ} (hN : LCanon 12 7 111 N) (hY : LCanon 12 7 111 Y)
    (h : blkM Y = lastCols (blkM Y) * blkM N) : sameSpanL CFSG.KD.LyOm.BC N Y = true := by
  obtain ⟨c, e⟩ := SpanC.bMul7_last_sound hBC hN hY
  have h1 : bMul7 CFSG.KD.LyOm.BC (last7 CFSG.KD.LyOm.BC Y) N = Y := blkM_inj c hY (by rw [e, ← h])
  unfold sameSpanL
  rw [h1]
  exact Nat.beq_refl Y

theorem tabX_sound {C : BConsts} {PI XM : ℕ → ℕ} {P nc : ℕ} (h : tabX C PI XM P nc = true) :
    ∀ c < 8, c < nc → fVld C (XM c) = true ∧
      Nat.beq (fMul C (PI c) (XM c)) (fMul C P (PI c)) = true := by
  intro c hc8 hc
  unfold tabX at h
  have := recAnd (p := fun c => bIf(Nat.blt c nc, bAnd(fVld C (XM c),
    Nat.beq (fMul C (PI c) (XM c)) (fMul C P (PI c))), true)) 8 h c hc8
  exact bAnd_true (bIf_true this (by rw [Nat.blt_eq]; exact hc))

theorem sum_blocks (k : ℕ) (f : ℕ → ℕ) :
    ∑ b ∈ Finset.range k, ∑ i ∈ Finset.Ico (64 * b) (64 * (b + 1)), f i =
      ∑ i ∈ Finset.range (64 * k), f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]

theorem cFix_total {KX PT XM : ℕ → ℕ} {n k : ℕ} (hn : n ≤ 64 * k) :
    ∑ b ∈ Finset.range k, cFix CFSG.KD.LyOm.BC KX PT XM n b 1 =
      ((Finset.range n).filter fun i => sameSpanL CFSG.KD.LyOm.BC (getRec KX 9324 i)
        (bMul CFSG.KD.LyOm.BC (getRec KX 9324 i) (XM (chartOf (getRec PT 32 i)))) = true).card := by
  classical
  simp only [cFix_eq, Finset.card_filter]
  rw [sum_blocks k (fun i => if i < n ∧ sameSpanL CFSG.KD.LyOm.BC (getRec KX 9324 i)
      (bMul CFSG.KD.LyOm.BC (getRec KX 9324 i) (XM (chartOf (getRec PT 32 i)))) = true then 1 else 0),
    show 64 * k = n + (64 * k - n) by omega, Finset.sum_range_add,
    Finset.sum_eq_zero (s := Finset.range (64 * k - n)) (fun i _ => if_neg (by omega)), Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => by
    rw [if_congr (and_iff_right (Finset.mem_range.1 hi)) rfl rfl]

@[expose] def o1sp (i : ℕ) : LySp := ⟨rs (blkM (getRec CFSG.KD.LyO1.KX 9324 i) *
  bigM (CFSG.KD.LyO1.PJ (chartOf (getRec CFSG.KD.LyO1.PT 32 i))) * TIm)⟩

theorem o1_node_ok
    [LySeed] {x : J} {XM : ℕ → ℕ} {P : ℕ} (cP : LCanon 12 111 111 P)
    (hP : Tm * bigM P * TIm = (mat x)ᵀ)
    (hX : tabX CFSG.KD.LyOm.BC CFSG.KD.LyO1.PI XM P CFSG.KD.LyO1.nc = true) {i : ℕ}
    (hi : i < CFSG.KD.LyO1.n) (hfix : x • o1sp i = o1sp i) :
    sameSpanL CFSG.KD.LyOm.BC (getRec CFSG.KD.LyO1.KX 9324 i)
      (bMul CFSG.KD.LyOm.BC (getRec CFSG.KD.LyO1.KX 9324 i)
        (XM (chartOf (getRec CFSG.KD.LyO1.PT 32 i)))) = true := by
  have hnc : CFSG.KD.LyO1.nc ≤ 8 := by rw [CFSG.KD.LyO1.nc_eq]
  obtain ⟨hcan, -, -⟩ := o1_tree
  obtain ⟨cN, hch, hlast⟩ := hcan i hi
  set N := blkM (getRec CFSG.KD.LyO1.KX 9324 i)
  set c := chartOf (getRec CFSG.KD.LyO1.PT 32 i)
  set PI := bigM (CFSG.KD.LyO1.PI c)
  set PJ := bigM (CFSG.KD.LyO1.PJ c)
  have hPI := tabPI_sound CFSG.KD.LyOm.o1pi c (by omega) hch
  have cPI := fvld_canon hPI.1
  have cPJ := fvld_canon hPI.2.1
  have ePI : PI * PJ = 1 := by
    rw [← (fmul cPI cPJ).2, beq_eq hPI.2.2, one_facts.2]
  have ePJ : PJ * PI = 1 := mul_comm_one ePI
  obtain ⟨vX, eX⟩ := tabX_sound hX c (by omega) hch
  have cX := fvld_canon vX
  have mX : PI * bigM (XM c) = bigM P * PI := by
    rw [← (fmul cPI cX).2, beq_eq eX, (fmul cP cPI).2]
  have hJP : PJ * bigM P = bigM (XM c) * PJ := by
    calc PJ * bigM P = PJ * (bigM P * PI) * PJ := by
          simp only [Matrix.mul_assoc, ePI, Matrix.mul_one]
      _ = PJ * (PI * bigM (XM c)) * PJ := by rw [mX]
      _ = bigM (XM c) * PJ := by
          rw [← Matrix.mul_assoc, ePJ, Matrix.one_mul]
  have hfix' := hfix
  change x • (⟨rs (N * PJ * TIm)⟩ : LySp) = ⟨rs (N * PJ * TIm)⟩ at hfix'
  rw [smul_rs] at hfix'
  have e1 : N * PJ * TIm * (mat x)ᵀ = N * bigM (XM c) * (PJ * TIm) := by
    rw [← hP]
    calc N * PJ * TIm * (Tm * bigM P * TIm) = N * (PJ * (TIm * Tm) * bigM P) * TIm := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [t_facts.2, Matrix.mul_one, hJP]
          simp only [Matrix.mul_assoc]
  have hle' : rs (N * bigM (XM c) * (PJ * TIm)) ≤ rs (N * PJ * TIm) := by
    rw [← e1]
    exact (congrArg LySp.V hfix').le
  obtain ⟨A, hA⟩ := exists_mul_of_le hle'
  have hNX : N * bigM (XM c) = A * N := by
    have h1 := congrArg (· * (Tm * PI)) hA
    have r1 : N * bigM (XM c) * (PJ * TIm) * (Tm * PI) = N * bigM (XM c) := by
      calc N * bigM (XM c) * (PJ * TIm) * (Tm * PI)
          = N * bigM (XM c) * (PJ * (TIm * Tm) * PI) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [t_facts.2, Matrix.mul_one, ePJ, Matrix.mul_one]
    have r2 : A * (N * PJ * TIm) * (Tm * PI) = A * N := by
      calc A * (N * PJ * TIm) * (Tm * PI) = A * N * (PJ * (TIm * Tm) * PI) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [t_facts.2, Matrix.mul_one, ePJ, Matrix.mul_one]
    change N * bigM (XM c) * (PJ * TIm) * (Tm * PI) = A * (N * PJ * TIm) * (Tm * PI) at h1
    rw [r1, r2] at h1
    exact h1
  have b := bmul cN cX
  refine sameSpanL_complete cN b.1 ?_
  have hl : lastCols (A * N) = A := by
    have : lastCols (A * N) = A * lastCols N := by
      ext a k
      simp [lastCols, Matrix.mul_apply]
    rw [this, hlast, Matrix.mul_one]
  rw [b.2, hNX, hl]

theorem o1_fix_le
    [LySeed] (ho : Nat.card (orbit lyH (gRep 1 • opE)) = 19530) {x : J}
    (hx : x ∈ lyH) {XM : ℕ → ℕ} {P : ℕ} (cP : LCanon 12 111 111 P)
    (hP : Tm * bigM P * TIm = (mat x)ᵀ)
    (hX : tabX CFSG.KD.LyOm.BC CFSG.KD.LyO1.PI XM P CFSG.KD.LyO1.nc = true) :
    Nat.card {y : orbit lyH (gRep 1 • opE) // (⟨x, hx⟩ : lyH) • y = y} ≤
      ∑ b ∈ Finset.range 306, cFix CFSG.KD.LyOm.BC CFSG.KD.LyO1.KX CFSG.KD.LyO1.PT XM
        CFSG.KD.LyO1.n b 1 := by
  classical
  have hn := CFSG.KD.LyO1.n_eq
  rw [cFix_total (by rw [hn]; norm_num), ← card_fin_filter]
  obtain ⟨-, hmem, hinj⟩ := o1_tree
  let g : Fin CFSG.KD.LyO1.n → orbit lyH (imOp (gRep 1 • opE)) := fun i => ⟨o1sp i.val, hmem i.val i.2⟩
  have hgi : Function.Injective g := fun i j e =>
    Fin.ext (hinj i.val i.2 j.val j.2 (congrArg LySp.V (congrArg Subtype.val e)))
  have hfin : Finite (orbit lyH (gRep 1 • opE)) := Set.finite_coe_iff.2 (Set.toFinite _)
  have hle := card_orbit_le_of_map (G := lyH) imOp (imOp_smulS lyH) (gRep 1 • opE)
  have hgb : Function.Bijective g := hgi.bijective_of_nat_card_le (by
    rw [Nat.card_eq_fintype_card (α := Fin CFSG.KD.LyO1.n), Fintype.card_fin, hn]
    omega)
  let ψ : orbit lyH (gRep 1 • opE) → orbit lyH (imOp (gRep 1 • opE)) := fun y =>
    ⟨imOp y.1, by
      obtain ⟨h, hh⟩ := y.2
      refine ⟨h, ?_⟩
      change h • imOp (gRep 1 • opE) = imOp y.1
      rw [← imOp_smulS, ← hh]⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨_, h, rfl⟩
    exact ⟨⟨h • (gRep 1 • opE), h, rfl⟩, Subtype.ext (imOp_smulS lyH h _)⟩
  have hψb : Function.Bijective ψ := hψs.bijective_of_nat_card_le (by
    rw [ho]
    have := Nat.card_le_card_of_injective g hgi
    rw [Nat.card_eq_fintype_card (α := Fin CFSG.KD.LyO1.n), Fintype.card_fin, hn] at this
    exact this)
  let e := Equiv.ofBijective g hgb
  have key : ∀ y : orbit lyH (gRep 1 • opE), (⟨x, hx⟩ : lyH) • y = y →
      sameSpanL CFSG.KD.LyOm.BC (getRec CFSG.KD.LyO1.KX 9324 (e.symm (ψ y)).val)
        (bMul CFSG.KD.LyOm.BC (getRec CFSG.KD.LyO1.KX 9324 (e.symm (ψ y)).val)
          (XM (chartOf (getRec CFSG.KD.LyO1.PT 32 (e.symm (ψ y)).val)))) = true := by
    intro y hy
    refine o1_node_ok cP hP hX (e.symm (ψ y)).isLt ?_
    have hsp : o1sp (e.symm (ψ y)).val = imOp y.1 := congrArg Subtype.val (e.apply_symm_apply (ψ y))
    rw [hsp, ← imOp_smul]
    have := congrArg Subtype.val hy
    exact congrArg imOp this
  let φ : {y : orbit lyH (gRep 1 • opE) // (⟨x, hx⟩ : lyH) • y = y} →
      {i : Fin CFSG.KD.LyO1.n // sameSpanL CFSG.KD.LyOm.BC (getRec CFSG.KD.LyO1.KX 9324 i.val)
        (bMul CFSG.KD.LyOm.BC (getRec CFSG.KD.LyO1.KX 9324 i.val)
          (XM (chartOf (getRec CFSG.KD.LyO1.PT 32 i.val)))) = true} := fun y =>
    ⟨e.symm (ψ y.1), key y.1 y.2⟩
  have hφ : Function.Injective φ := by
    intro y z h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (hψb.1 (e.symm.injective h1))
  exact Nat.card_le_card_of_injective φ hφ

end CertificateChecks.KernelLy.Omega

end

end
