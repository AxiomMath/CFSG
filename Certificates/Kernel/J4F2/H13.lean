
module

public import CFSG.Quasithin.H13.J4CoreInputs
public import CFSG.Quasithin.H13.J4WordsBase
public import CFSG.Certificates.ExtraspecialNormalForm
public import CFSG.Quasithin.H13.J4TypeCheckInputs
public import CFSG.Quasithin.H13.J4CoreBase
public import CFSG.Quasithin.H13.J4WordsInputs
public import CFSG.Quasithin.H13.J4Defs
public import CFSG.Quasithin.H13.J4ChainSpec
public import Certificates.Data.CFSGNative.H13.J4Elems
public import Certificates.Kernel.J4F2.Pair
public import Certificates.Kernel.J4Q.Mat
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4F2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native
open CFSG.Quasithin.H13.J4 CertificateChecks.KernelJ4Q

theorem mkIte {p : Prop} [Decidable p] {X Y : Array V2} {x y : Nat} (hX : WfA X ∧ encR X = x)
    (hY : WfA Y ∧ encR Y = y) : WfA (if p then X else Y) ∧ encR (if p then X else Y) =
      if p then x else y := by
  split
  · exact hX
  · exact hY

theorem pe_getD_map (L : List Nat) {f : Nat → Pr} {fK : Nat → Nat × Nat}
    (h : ∀ i, PE (f i) (fK i)) (a : Nat) : PE ((L.map f).getD a (prOne ())) ((L.map fK).getD a prOneK) := by
  by_cases ha : a < L.length
  · rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getD_eq_getElem _ _ (by simpa using ha),
      List.getElem_map, List.getElem_map]
    exact h _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    exact pe_one

@[expose] noncomputable def uvK : List (Nat × Nat) :=
  [prWordK baseK (uLetters ()), prWordK baseK (vLetters ())]

theorem pt_pair {x y : Pr} {a b : Nat × Nat} (hx : PE x a) (hy : PE y b) : PT #[x, y] [a, b] := by
  intro k
  rcases k with _ | _ | k
  · exact hx
  · exact hy
  · exact pe_one

theorem pt_uv : PT (uvPairsOf (basePairs ())) uvK := by
  unfold uvPairsOf uvK
  exact pt_pair (pe_word pt_base _) (pe_word pt_base _)

@[expose] noncomputable def dK : Nat × Nat :=
  prMulK (prMulK (prMulK (prInvK (uvK.getD 1 prOneK)) (uvK.getD 0 prOneK)) (uvK.getD 1 prOneK))
    (uvK.getD 0 prOneK)

theorem pe_d : PE (dOf (uvPairsOf (basePairs ()))) dK :=
  pe_mul (pe_mul (pe_mul (pe_inv (pt_uv 1)) (pt_uv 0)) (pt_uv 1)) (pt_uv 0)

@[expose] noncomputable def tK : Nat × Nat := prPowK dK 22

theorem pe_t : PE (tOf (uvPairsOf (basePairs ()))) tK := pe_pow pe_d 22

@[expose] noncomputable def rcK (cw : List Int) : Nat × Nat :=
  prMulK (prMulK (prWordK uvK cw) (prPowK dK 11)) (prInvK (prWordK uvK cw))

theorem pe_rc (cw : List Int) : PE (rConjOf (uvPairsOf (basePairs ())) cw) (rcK cw) :=
  pe_mul (pe_mul (pe_word pt_uv cw) (pe_pow pe_d 11)) (pe_inv (pe_word pt_uv cw))

@[expose] noncomputable def rPairsK : List (Nat × Nat) :=
  (List.range 12).map fun i => rcK (coreBasisConjugators.getD i [])

theorem pt_r : PT rPairs rPairsK :=
  pt_ofList _ _ (fun i => pe_rc (coreBasisConjugators.getD i [])) 12

@[expose] noncomputable def rProdK (l : List Nat) : Nat × Nat :=
  l.foldl (fun acc i => prMulK acc (rPairsK.getD i prOneK)) prOneK

theorem pe_rProd (l : List Nat) : PE (rProdPair l) (rProdK l) := pe_fold pt_r l pe_one

@[expose] noncomputable def qProdK (l : List Nat) : Nat × Nat :=
  l.foldl (fun acc a => prMulK acc (rProdK (qIdx.getD a []))) prOneK

theorem pe_qProd (l : List Nat) : PE (qProdPair l) (qProdK l) :=
  pe_fold (fun a => pe_rProd (qIdx.getD a [])) l pe_one

@[expose] noncomputable def pChecksK : Bool :=
  let qs := (List.range 12).map fun a => rProdK (qIdx.getD a [])
  (List.range 12).all (fun a =>
    Nat.beq (mulJ c rm (qs.getD a prOneK).1 (qs.getD a prOneK).1) one) &&
  (List.range 12).all (fun a => (List.range 12).all fun b =>
    Nat.beq (mulJ c rm (qs.getD a prOneK).1 (qs.getD b prOneK).1)
      (if (cRows.getD a 0).testBit b
        then mulJ c rm (mulJ c rm (qs.getD b prOneK).1 (qs.getD a prOneK).1) tK.1
        else mulJ c rm (qs.getD b prOneK).1 (qs.getD a prOneK).1)) &&
  (List.range 12).all fun i =>
    Nat.beq (rPairsK.getD i prOneK).1
      (if ((rExpr.getD i (0, [])).1 = 1)
        then mulJ c rm tK.1 (qProdK (rExpr.getD i (0, [])).2).1
        else (qProdK (rExpr.getD i (0, [])).2).1)

theorem pChecksK_ok : pChecksK = true := by quickRfl

theorem pChecks_eq : pChecks = pChecksK := by
  unfold pChecks pChecksK
  simp only []
  have hq := pe_getD_map (List.range 12) (fun a => pe_rProd (qIdx.getD a []))
  congr 1
  · congr 1
    · apply mkRange_congr
      intro a _
      exact mkEq (mkMul (hq a).1 (hq a).1) mkId
    · apply mkRange_congr
      intro a _
      apply mkRange_congr
      intro b _
      exact mkEq (mkMul (hq a).1 (hq b).1)
        (mkIte (mkMul (mkMul (hq b).1 (hq a).1) pe_t.1) (mkMul (hq b).1 (hq a).1))
  · apply mkRange_congr
    intro i _
    exact mkEq (pt_r i).1 (mkIte (mkMul pe_t.1 (pe_qProd _).1) (pe_qProd _).1)

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native CFSG.Certificates.ExtraspecialNF in
theorem c7012 :
    pChecks = true := pChecks_eq.trans pChecksK_ok

theorem matChecks_ok : CFSG.Sporadic.J4.Native.matChecks = true := by
  have h := matFacts
  unfold CFSG.Sporadic.J4.Native.matChecks
  simp only []
  rw [h.baseInv, h.locInv, h.locFix, h.locSize, h.stabSize, h.a2, h.a1, h.b4, h.b2,
    h.ab37, h.ab1, h.cinv, h.z43, h.z1, h.formA, h.formB]
  rfl

theorem t_chk : (Nat.beq (mulJ c rm tK.1 (uvK.getD 0 prOneK).1) (mulJ c rm (uvK.getD 0 prOneK).1 tK.1) &&
    Nat.beq (mulJ c rm tK.1 (uvK.getD 1 prOneK).1) (mulJ c rm (uvK.getD 1 prOneK).1 tK.1) &&
    Nat.beq (mulJ c rm tK.1 tK.1) one && neN tK.1 one) = true := by quickRfl

theorem tChecks_ok : tChecks = true := by
  unfold tChecks
  simp only []
  have h := t_chk
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, rowsNe_of pe_t.1 mkId h4⟩
  · rw [mkEq (mkMul pe_t.1 (pt_uv 0).1) (mkMul (pt_uv 0).1 pe_t.1)]
    exact h1
  · rw [mkEq (mkMul pe_t.1 (pt_uv 1).1) (mkMul (pt_uv 1).1 pe_t.1)]
    exact h2
  · rw [mkEq (mkMul pe_t.1 pe_t.1) mkId]
    exact h3

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4 in
open CFSG.Sporadic.J4.Native CFSG.Quasithin.H13.J4.Native in
theorem c7018 :
    (CFSG.Sporadic.J4.Native.matChecks = true)
    ∧ (tChecks = true) := ⟨matChecks_ok, tChecks_ok⟩

theorem pe_tP : PE tPair tK := pe_t

@[expose] noncomputable def w0K : Nat × Nat := prPowK (prWordK uvK ntWord) 11

theorem pe_w0 : PE w0Pair w0K := pe_pow (pe_word pt_uv ntWord) 11

@[expose] noncomputable def w0cK : Nat × Nat :=
  prMulK (prMulK (prMulK w0K (rPairsK.getD 0 prOneK)) (prInvK w0K)) (prInvK (rPairsK.getD 0 prOneK))

theorem w0_chk : (neN w0cK.1 one && neN w0cK.1 tK.1) = true := by quickRfl

theorem w0Check_ok : w0Check = true := by
  unfold w0Check
  simp only []
  have hc : PE (prMul (prMul (prMul w0Pair (rPairs[0]?.getD (prOne ()))) (prInv w0Pair))
      (prInv (rPairs[0]?.getD (prOne ())))) w0cK :=
    pe_mul (pe_mul (pe_mul pe_w0 (pt_r 0)) (pe_inv pe_w0)) (pe_inv (pt_r 0))
  have h := w0_chk
  simp only [Bool.and_eq_true] at h ⊢
  exact ⟨rowsNe_of hc.1 mkId h.1, rowsNe_of hc.1 pe_t.1 h.2⟩

@[expose] noncomputable def hypK (k : Nat) : Nat × Nat := rProdK (hypList k)

theorem pe_hyp (k : Nat) : PE (hypPair k) (hypK k) := pe_rProd (hypList k)

@[expose] noncomputable def plusChecksK : Bool :=
  (List.range 6).all (fun i =>
    Nat.beq (prMulK (hypK (2 * i)) (hypK (2 * i))).1 one &&
      Nat.beq (prMulK (hypK (2 * i + 1)) (hypK (2 * i + 1))).1 one &&
      Nat.beq (prMulK (prMulK (hypK (2 * i)) (hypK (2 * i + 1)))
        (prMulK (hypK (2 * i)) (hypK (2 * i + 1)))).1 tK.1) &&
  (List.range 6).all fun i => (List.range 6).all fun j =>
    i == j ||
      (Nat.beq (prMulK (hypK (2 * i)) (hypK (2 * j))).1 (prMulK (hypK (2 * j)) (hypK (2 * i))).1 &&
        Nat.beq (prMulK (hypK (2 * i)) (hypK (2 * j + 1))).1
          (prMulK (hypK (2 * j + 1)) (hypK (2 * i))).1 &&
        Nat.beq (prMulK (hypK (2 * i + 1)) (hypK (2 * j + 1))).1
          (prMulK (hypK (2 * j + 1)) (hypK (2 * i + 1))).1)

theorem plusChecksK_ok : plusChecksK = true := by quickRfl

theorem plusChecks_eq : plusChecks = plusChecksK := by
  unfold plusChecks plusChecksK
  simp only []
  congr 1
  · apply mkRange_congr
    intro i _
    rw [mkEq (pe_mul (pe_hyp _) (pe_hyp _)).1 mkId, mkEq (pe_mul (pe_hyp _) (pe_hyp _)).1 mkId,
      mkEq (pe_mul (pe_mul (pe_hyp _) (pe_hyp _)) (pe_mul (pe_hyp _) (pe_hyp _))).1 pe_tP.1]
  · apply mkRange_congr
    intro i _
    apply mkRange_congr
    intro j _
    rw [mkEq (pe_mul (pe_hyp _) (pe_hyp _)).1 (pe_mul (pe_hyp _) (pe_hyp _)).1,
      mkEq (pe_mul (pe_hyp (2 * i)) (pe_hyp (2 * j + 1))).1 (pe_mul (pe_hyp _) (pe_hyp _)).1,
      mkEq (pe_mul (pe_hyp (2 * i + 1)) (pe_hyp (2 * j + 1))).1 (pe_mul (pe_hyp _) (pe_hyp _)).1]

@[expose] noncomputable def hypProdK (l : List Nat) : Nat × Nat :=
  l.foldl (fun acc k => prMulK acc (hypK k)) prOneK

theorem pe_hypProd (l : List Nat) : PE (hypProdPair l) (hypProdK l) := pe_fold pe_hyp l pe_one

@[expose] noncomputable def genChecksK : Bool :=
  (List.range 12).all fun j =>
    Nat.beq (rPairsK.getD j prOneK).1
      (prMulK (prPowK tK (rExprH.getD j ([], 0)).2) (hypProdK (rExprH.getD j ([], 0)).1)).1

theorem genChecksK_ok : genChecksK = true := by quickRfl

theorem genChecks_eq : genChecks = genChecksK := by
  unfold genChecks genChecksK
  simp only []
  apply mkRange_congr
  intro j _
  exact mkEq (pt_r j).1 (pe_mul (pe_pow pe_t _) (pe_hypProd _)).1

@[expose] noncomputable def weakK : Nat × Nat :=
  prMulK (prPowK (prMulK tK (prMulK (prMulK (prInvK (prWordK baseK weakWord)) (hypK 0))
    (prWordK baseK weakWord))) 6) (prInvK (prWordK baseK weakWord))

theorem pe_weak : PE weakPair weakK :=
  pe_mul (pe_pow (pe_mul pe_t (pe_mul (pe_mul (pe_inv (pe_word pt_base weakWord)) (pe_hyp 0))
    (pe_word pt_base weakWord))) 6) (pe_inv (pe_word pt_base weakWord))

theorem weak_chk : (Nat.beq (prMulK (prMulK (prInvK weakK) tK) weakK).1 (hypK 0).1 &&
    neN (hypK 0).1 tK.1) = true := by quickRfl

theorem weakChecks_ok : weakChecks = true := by
  unfold weakChecks
  have h := weak_chk
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨?_, rowsNe_of (pe_hyp 0).1 pe_t.1 h.2⟩
  rw [mkEq (pe_mul (pe_mul (pe_inv pe_weak) pe_tP) pe_weak).1 (pe_hyp 0).1]
  exact h.1

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.J4 CFSG.Sporadic.J4.Native in
open CFSG.Quasithin.H13.J4.Native in
theorem c7017 :
    (w0Check = true)
    ∧ (plusChecks = true)
    ∧ (genChecks = true)
    ∧ (weakChecks = true) :=
  ⟨w0Check_ok, plusChecks_eq.trans plusChecksK_ok, genChecks_eq.trans genChecksK_ok,
    weakChecks_ok⟩

end CertificateChecks.KernelJ4F2

end
