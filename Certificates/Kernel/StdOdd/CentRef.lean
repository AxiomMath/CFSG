module

public import Certificates.Kernel.StdOdd.CentAssemble

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix CFSG.KC.LQT.P

@[expose] def segsL : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | _, [] => []
  | f + 1, n :: t => t.take n :: segsL f (t.drop n)

namespace CentData

variable (D : CentData)

@[expose] noncomputable def refF (A B : ℕ) (O : List ℕ) (Sr : List (List (List ℕ))) (m r : ℕ) :
    Bool :=
  andB (andB (Nat.beq (lenN O) D.p) (andB (Nat.ble 1 m) (Nat.blt m D.p)))
    (andB (refOK (D.xB A B) A B O D.eL ((List.range (m - 1)).map fun l => (D.RI (l + 1)).map (nthV D.V))
      Sr D.βs (D.FP m) (D.nf m) m) (Nat.beq (nthN O 0) (nthN D.reps r)))

@[expose] noncomputable def covF (sidx : ℕ → ℕ) (R : ℕ) : Bool :=
  allN (lenN D.reps) fun r =>
    (!(Nat.beq (nthN D.st r) 1)) || (List.range R).any fun ri => Nat.beq (sidx ri) r

end CentData

theorem refs_of_checks (D : CentData) {A B : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (hv0 : Nat.beq (nthV D.V 0) A = true)
    (hv1 : Nat.beq (nthV D.V 1) B = true) (hp : ∀ t < lenLL D.prog, slpLine D.V D.prog 2 t = true)
    (hn : Nat.beq (lenN D.V) (Nat.add 2 (lenLL D.prog)) = true)
    (hbase : D.baseOK A B = true) (hlev : ∀ j < D.p - 1, D.levOK (j + 1) = true)
    (heL : D.eL.length = D.p) (helt : ∀ i < D.p, D.e i < D.p) (he0 : D.e 0 = 0)
    {R : ℕ} {O : ℕ → List ℕ} {Sr : ℕ → List (List (List ℕ))} {fl sidx : ℕ → ℕ}
    (hchk : ∀ ri < R, D.refF A B (O ri) (Sr ri) (fl ri) (sidx ri) = true)
    (hcov : D.covF sidx R = true) :
    ∀ r < lenN D.reps, nthN D.st r = 1 → D.RefFact (vecK (nthN D.reps r)) := by
  have hX : Rep (D.xB A B) (wM D.xw) := rep_wM hA hB D.xw
  have hV : ∀ i < lenN D.V, Rep (nthV D.V i) (vM D.prog i) := fun i hi =>
    rep_vM hA hB hv0 hv1 hp hn hi
  simp only [CentData.baseOK, andB_eq, Bool.and_eq_true] at hbase
  obtain ⟨⟨⟨⟨hb, hβ⟩, -⟩, -⟩, -⟩ := hbase
  have hbv : vecK D.bv = D.bK := by
    have := map1_K (rep_wM hA hB D.d0) hb
    rw [vecK_e7] at this
    exact this.symm
  have hβv : ∀ j < D.p, vecK (nthN D.βs j) = D.βK j := by
    intro j hj
    have := map1_K (rep_powB hX (nthN D.eL j)) (allN_true hβ j hj)
    rw [hbv, nthN_eq_getD] at this
    exact this.symm
  have hRI : ∀ j, 1 ≤ j → j < D.p → ∀ r ∈ D.RI j, r < lenN D.V := by
    intro j h1 h2 r hr
    have h := hlev (j - 1) (by omega)
    rw [Nat.sub_add_cancel h1] at h
    simp only [CentData.levOK, andB_eq, Bool.and_eq_true] at h
    have := allL_true h.1 r hr
    rw [Bool.and_eq_true] at this
    exact Nat.blt_eq.mp this.1
  intro r hr hs
  have hc := allN_true hcov r hr
  rw [Bool.or_eq_true, Bool.not_eq_true', hs] at hc
  rcases hc with hc | hc
  · exact absurd hc (by decide)
  obtain ⟨ri, hri, hre⟩ := List.any_eq_true.1 hc
  rw [List.mem_range] at hri
  have hsr : sidx ri = r := Nat.eq_of_beq_eq_true hre
  have h := hchk ri hri
  simp only [CentData.refF, andB_eq, Bool.and_eq_true] at h
  obtain ⟨⟨hlen, hm1, hmp⟩, href, h0⟩ := h
  have hO : (O ri).length = D.p := by
    rw [← CFSG.KS.StdOdd.Chain.lenN_eq_length]
    exact Nat.eq_of_beq_eq_true hlen
  have hf := refFact_of_refOK D hA hB hV hRI hβv heL helt he0 (Nat.le_of_ble_eq_true hm1)
    (Nat.blt_eq.mp hmp) hO href
  rwa [Nat.eq_of_beq_eq_true h0, hsr] at hf

end CFSG.KD.StdOdd.Cent

end
