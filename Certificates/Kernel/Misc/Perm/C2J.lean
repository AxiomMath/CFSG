module

public import Certificates.Kernel.Misc.Perm.C2I
public import CFSG.RankThree.Native.F2EnumPoint
public import Certificates.Kernel.Misc.Perm.C2E

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer (ArrCert)

theorem get2_0 {α : Type} [Inhabited α] (a b : α) : #[a, b][0]! = a := rfl

theorem get2_1 {α : Type} [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem get3_0 {α : Type} [Inhabited α] (a b c : α) : #[a, b, c][0]! = a := rfl

theorem get3_1 {α : Type} [Inhabited α] (a b c : α) : #[a, b, c][1]! = b := rfl

theorem get3_2 {α : Type} [Inhabited α] (a b c : α) : #[a, b, c][2]! = c := rfl

theorem GD0 : GD 0 = DG0 := rfl

theorem of_chunk {f : ℕ → Bool} {lo cnt : ℕ} (h : allN cnt (fun t => f (Nat.add lo t)) = true)
    {i : ℕ} (h1 : lo ≤ i) (h2 : i < lo + cnt) : f i = true := by
  have := allN_spec h (i - lo) (by omega)
  have e : Nat.add lo (i - lo) = i := by
    simp only [Nat.add_eq]
    omega
  rwa [e] at this

@[expose] noncomputable def keyAt (c N : ℕ) (PM : ℕ → ℕ) (j : ℕ) : Bool :=
  Nat.blt (SO c j) N && Nat.beq (SOI c (SO c j)) j &&
    (!(Nat.blt (Nat.add j 1) N) || Nat.blt (keyK PM (SO c j)) (keyK PM (SO c (Nat.add j 1))))

@[expose] noncomputable def ptAt (ngen N : ℕ) (GM PM : ℕ → ℕ) (HE HR HL : ℕ → ℕ) (i : ℕ) : Bool :=
  pointM mmK ngen N GM PM (fun i k => f12 (HE i) k) (fun i => f12 (HR 0) i) (fun i => f12 (HL 0) i) i

theorem enum_of {ngen N cI : ℕ} {GM GMI PM HE HR HL : ℕ → ℕ} {gs : Array (Array ℕ)}
    {c : ArrCert} (hgs : gs.size = ngen) (hG : ∀ k < ngen, gs[k]! = permOfMat 22 co2FiveV (GM k))
    (hGI : ∀ k < ngen, Inv 22 co2FiveV (GM k) (GMI k)) (hN : c.pts.size = N)
    (hP : ∀ i < N, c.pts[i]! = permOfMat 22 co2FiveV (PM i))
    (hE : ∀ i < N, (c.edges[i]!).size = ngen ∧ ∀ k < ngen, (c.edges[i]!)[k]! = f12 (HE i) k)
    (hPL : ∀ i < N, c.par[i]! = f12 (HR 0) i ∧ c.lab[i]! = f12 (HL 0) i)
    (h0 : 0 < N) (hroot : Nat.beq (PM 0) I22 = true)
    (hp : ∀ i < N, ptAt ngen N GM PM HE HR HL i = true) (hk : ∀ j < N, keyAt cI N PM j = true) :
    enumOK 2300 gs co2FiveKeyPts c = true := by
  have h := enumOK_of_pointM sys hvm hmm I22_eq hgs hG hGI (ps := co2FiveKeyPts)
    (by rw [V_size]; decide) hN hP hE hPL h0 (Nat.eq_of_beq_eq_true hroot) hp
    (SO := SO cI) (SOI := SOI cI)
    (fun j hj => by
      have := hk j hj
      unfold keyAt at this
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
      exact ⟨this.1.1, this.1.2⟩)
    (fun j hj => by
      have := hk j (by omega)
      unfold keyAt at this
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at this
      rcases this.2 with h' | h'
      · have h2 : Nat.blt (Nat.add j 1) N = true := by rw [Nat.blt_eq]; exact hj
        rw [h'] at h2
        exact absurd h2 Bool.false_ne_true
      · rw [V_size]
        exact h')
  rwa [V_size] at h

theorem ptQ_all : ∀ i < 125, ptAt 2 125 GQ PQ HQE.F HQR.F HQL.F i = true :=
  fun i hi => of_chunk (f := ptAt 2 125 GQ PQ HQE.F HQR.F HQL.F) ptsQ_0 (Nat.zero_le i) hi

theorem ptC0_all : ∀ i < 3000, ptAt 2 3000 GC0 PC0 HC0E.F HC0R.F HC0L.F i = true :=
  allN_of_chunks (c := 500) (n := 6) (f := ptAt 2 3000 GC0 PC0 HC0E.F HC0R.F HC0L.F) ptsC0_chunks

theorem ptC1_all : ∀ i < 600, ptAt 3 600 GC1 PC1 HC1E.F HC1R.F HC1L.F i = true :=
  allN_of_chunks (c := 100) (n := 6) (f := ptAt 3 600 GC1 PC1 HC1E.F HC1R.F HC1L.F) ptsC1_chunks

theorem ptD_all : ∀ i < 60, ptAt 2 60 GD PD HDE.F HDR.F HDL.F i = true :=
  fun i hi => of_chunk (f := ptAt 2 60 GD PD HDE.F HDR.F HDL.F) ptsD_0 (Nat.zero_le i) hi

theorem enumQ : enumOK 2300 co2FiveQGenArrs co2FiveKeyPts co2FiveQLit = true := by
  obtain ⟨hN, hP, hE, hPL⟩ := litQ
  refine enum_of (ngen := 2) (GM := GQ) (GMI := GQI) (cI := 0) (by rfl) ?_ ?_ hN hP hE hPL
    (by norm_num) rootQ ptQ_all
    (fun j hj => of_chunk (f := keyAt 0 125 PQ) keysQ_0 (Nat.zero_le j) hj)
  · intro k hk
    interval_cases k
    · rw [co2FiveQGenArrs, get2_0]
      exact arr_eq (k := 4) (by norm_num)
    · rw [co2FiveQGenArrs, get2_1]
      exact arr_eq (k := 5) (by norm_num)
  · intro k hk
    interval_cases k
    · exact (amF (k := 4) (by norm_num)).1
    · exact (amF (k := 5) (by norm_num)).1

theorem enumC0 : enumOK 2300 co2FiveC0GenArrs co2FiveKeyPts co2FiveC0Lit = true := by
  obtain ⟨hN, hP, hE, hPL⟩ := litC0
  refine enum_of (ngen := 2) (GM := GC0) (GMI := GC0I) (cI := 1) (by rfl) ?_ ?_ hN hP hE hPL
    (by norm_num) rootC0 ptC0_all ?_
  · intro k hk
    interval_cases k
    · rw [co2FiveC0GenArrs, get2_0]
      exact arr_eq (k := 2) (by norm_num)
    · rw [co2FiveC0GenArrs, get2_1]
      exact arr_eq (k := 3) (by norm_num)
  · intro k hk
    interval_cases k
    · exact (amF (k := 2) (by norm_num)).1
    · exact (amF (k := 3) (by norm_num)).1
  · exact allN_of_chunks (c := 500) (n := 6) (f := keyAt 1 3000 PC0) keysC0_chunks

theorem C1gen : ∀ k < 3, co2FiveC1GenArrs[k]! = permOfMat 22 co2FiveV (GC1 k) := by
  intro k hk
  interval_cases k
  · rw [co2FiveC1GenArrs, get3_0, co2FiveX1Arr]
    exact arr_eq (k := 1) (by norm_num)
  · rw [co2FiveC1GenArrs, get3_1]
    exact arr_eq (k := 6) (by norm_num)
  · rw [co2FiveC1GenArrs, get3_2]
    exact arr_eq (k := 7) (by norm_num)

theorem C1genI : ∀ k < 3, Inv 22 co2FiveV (GC1 k) (GC1I k) := by
  intro k hk
  interval_cases k
  · exact (amF (k := 1) (by norm_num)).1
  · exact (amF (k := 6) (by norm_num)).1
  · exact (amF (k := 7) (by norm_num)).1

theorem enumC1 : enumOK 2300 co2FiveC1GenArrs co2FiveKeyPts co2FiveC1Lit = true := by
  obtain ⟨hN, hP, hE, hPL⟩ := litC1
  refine enum_of (ngen := 3) (GM := GC1) (GMI := GC1I) (cI := 2) (by rfl) C1gen C1genI hN hP hE
    hPL (by norm_num) rootC1 ptC1_all
    (allN_of_chunks (c := 100) (n := 6) (f := keyAt 2 600 PC1) keysC1_chunks)

theorem inv_DG0 : Inv 22 co2FiveV DG0 DGI0 := by
  have h6 := (amF (k := 6) (by norm_num)).1
  have h7 := (amF (k := 7) (by norm_num)).1
  rw [DG0, DGI0, hmm, hmm, hmm, hmm, hmm, hmm]
  exact (h7.symm.mul hd22 h6.symm).mul hd22 (h7.mul hd22 h6)

theorem Dgen : ∀ k < 2, co2FiveDGenArrs[k]! = permOfMat 22 co2FiveV (GD k) := by
  intro k hk
  interval_cases k
  · have h := commutatorA_permOfMat hd22 sys.nodup sys.lt (C1genI 1 (by norm_num))
      (C1genI 2 (by norm_num))
    rw [V_size, ← C1gen 1 (by norm_num), ← C1gen 2 (by norm_num)] at h
    rw [co2FiveDGenArrs, get2_0, h, GD0, DG0, hmm, hmm, hmm]
    rfl
  · rw [co2FiveDGenArrs, get2_1]
    exact C1gen 2 (by norm_num)

theorem DgenI : ∀ k < 2, Inv 22 co2FiveV (GD k) (GDI k) := by
  intro k hk
  interval_cases k
  · exact inv_DG0
  · exact (amF (k := 7) (by norm_num)).1

theorem enumD : enumOK 2300 co2FiveDGenArrs co2FiveKeyPts co2FiveDLit = true := by
  obtain ⟨hN, hP, hE, hPL⟩ := litD
  exact enum_of (ngen := 2) (GM := GD) (GMI := GDI) (cI := 3) (by rfl) Dgen DgenI hN hP hE hPL
    (by norm_num) rootD
    ptD_all (fun j hj => of_chunk (f := keyAt 3 60 PD) keysD_0 (Nat.zero_le j) hj)

end CertificateChecks.KernelMisc.Co2K

end
