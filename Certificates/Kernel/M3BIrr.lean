module

public import CFSG.Certificates.Kernel.M3BIrr.MatSound
public import CFSG.Certificates.Kernel.M3BIrr.Checks
public import CFSG.Certificates.Kernel.M3BIrr.Spin0
public import CFSG.Certificates.Kernel.M3BIrr.Spin1
public import CFSG.Certificates.Kernel.M3BIrr.Spin2
public import CFSG.Certificates.Kernel.M3BIrr.Spin3

public section

namespace CertificateChecks.KernelM3BIrr

open Timmesfeld.M3B CFSG.HardMathSupport.MathTwE6.M3BIrr CFSG.KC.M3BIrr

@[expose] def EqE (A A' : Mat) : Prop := ∀ i j, mget A i j = mget A' i j

theorem mmul_congr {X X' A A' : Mat} (hX : EqE X X') (hA : EqE A A') : mmul X A = mmul X' A' := by
  unfold mmul
  congr 1
  funext i j
  congr 1
  funext k
  rw [hX i k, hA k j]

theorem mpow_congr {A A' : Mat} (hA : EqE A A') : ∀ n, mpow A n = mpow A' n
  | 0 => by rw [mpow.eq_def, mpow.eq_def]
  | n + 1 => by
    rw [mpow.eq_def, mpow.eq_def]
    dsimp only
    rw [mpow_congr hA n]
    exact mmul_congr (fun _ _ => rfl) hA

theorem vmul_congr {A A' : Mat} (hA : EqE A A') (x : Vec) : vmul x A = vmul x A' := by
  unfold vmul
  congr 1
  funext j
  congr 1
  funext k
  rw [hA k j]

theorem polyEval_congr {A A' : Mat} (hA : EqE A A') (cs : List ℕ) : polyEval cs A = polyEval cs A' := by
  unfold polyEval
  induction cs with
  | nil => simp only [List.foldr_nil]
  | cons c cs ih => rw [List.foldr_cons, List.foldr_cons, ih, mmul_congr hA (fun _ _ => rfl)]

theorem spinLoop_congr {A A' B B' : Mat} (hA : EqE A A') (hB : EqE B B') :
    ∀ n bas q, spinLoop A B n bas q = spinLoop A' B' n bas q
  | 0, bas, q => by simp only [spinLoop]
  | n + 1, bas, [] => by simp only [spinLoop]
  | n + 1, bas, x :: q => by
    simp only [spinLoop, vmul_congr hA, vmul_congr hB, spinLoop_congr hA hB n]

theorem idemOK_congr {A A' B B' : Mat} (hA : EqE A A') (hB : EqE B B') (i : ℕ) :
    idemOK A B i = idemOK A' B' i := by
  unfold idemOK spinFull
  simp only [polyEval_congr hA, spinLoop_congr hA hB]

theorem irrBody_congr {A A' B B' : Mat} (hA : EqE A A') (hB : EqE B B') :
    irrBody A B = irrBody A' B' := by
  unfold irrBody
  simp only [mpow_congr hA, mpow_congr hB, polyEval_congr hA, idemOK_congr hA hB]

theorem eqE_of_toM {A A' : Mat} (h : toM A = toM A') : EqE A A' := fun i j =>
  fz_inj (congrFun (congrFun h i) j)

theorem toM_pow2520 (G : Mat) : toM (pow2520 G) = toM (mpow G 2520) := by
  unfold pow2520
  simp only [toM_mpow, ← pow_mul]

theorem eqA : EqE (matA ()) CFSG.KD.M3BI.A0 :=
  eqE_of_toM ((toM_pow2520 _).symm.trans (toM_eq_of_meq CFSG.KD.M3BI.powA))

theorem eqB : EqE (matB ()) CFSG.KD.M3BI.B0 :=
  eqE_of_toM ((toM_pow2520 _).symm.trans (toM_eq_of_meq CFSG.KD.M3BI.powB))

theorem f3_cases (a : F3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  rcases a with ⟨_ | _ | _ | n, h⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · omega

theorem idemOK_of {A B : Mat} {i : ℕ}
    (h1 : meq (polyEval (idemCoeffs.getD i []) A) (mmul (matCi i) (matBi i)) = true)
    (h2 : CFSG.KD.M3BI.suppOK i = true) (h3 : ∀ a : F3, CFSG.KD.M3BI.spinAt A B i a = true) :
    idemOK A B i = true := by
  unfold idemOK
  simp only [Bool.and_eq_true]
  exact ⟨⟨h1, h2⟩, List.all_eq_true.2 fun a _ => h3 a⟩

theorem spins {A B : Mat} {i : ℕ} (h0 : CFSG.KD.M3BI.spinAt A B i 0 = true)
    (h1 : CFSG.KD.M3BI.spinAt A B i 1 = true) (h2 : CFSG.KD.M3BI.spinAt A B i 2 = true) :
    ∀ a : F3, CFSG.KD.M3BI.spinAt A B i a = true := fun a => by
  rcases f3_cases a with h | h | h
  · rw [h]; exact h0
  · rw [h]; exact h1
  · rw [h]; exact h2

open CFSG.KD.M3BI in
theorem body : irrBody CFSG.KD.M3BI.A0 CFSG.KD.M3BI.B0 = true := by
  have i0 := idemOK_of fac0 supp0 (spins spin0_0 spin0_1 spin0_2)
  have i1 := idemOK_of fac1 supp1 (spins spin1_0 spin1_1 spin1_2)
  have i2 := idemOK_of fac2 supp2 (spins spin2_0 spin2_1 spin2_2)
  have i3 := idemOK_of fac3 supp3 (spins spin3_0 spin3_1 spin3_2)
  unfold irrBody
  rw [ordA, ordB, idem, i0, i1, i2, i3]
  rfl

theorem irrCheck_true : irrCheck () = true := by
  rw [irrCheck_eq, irrBody_congr eqA eqB]
  exact body

end CertificateChecks.KernelM3BIrr

end
