module

public import Certificates.Kernel.Misc.Perm.C2H

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.HexFlat CFSG.RankThree.Native.F2
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer (ArrCert hexTable3)

@[expose] def Good (A : ℕ) : Prop :=
  (∀ v ∈ co2FiveV, vmul 22 v A ∈ co2FiveV) ∧ A < 2 ^ (22 * 22)

theorem good_mm {A B : ℕ} (hA : Good A) (hB : Good B) : Good (mmK A B) := by
  rw [hmm]
  exact ⟨maps_mmul hA.1 hB.1, mmul_lt _ _⟩

theorem good_I22 : Good I22 := ⟨maps_I22, by rw [I22_eq]; exact idM_lt⟩

theorem good_AM {k : ℕ} (hk : k < 38) : Good (AM k) := ⟨(amF hk).1.1, (amF hk).2.2⟩

theorem mpowW_succ (mm : ℕ → ℕ → ℕ) (I A e : ℕ) : mpowW mm I A (e + 1) = mm (mpowW mm I A e) A :=
  rfl

theorem pwK_succ (A e : ℕ) : pwK A (e + 1) = mmK (pwK A e) A := mpowW_succ mmK I22 A e

theorem good_pw {A : ℕ} (hA : Good A) : ∀ e, Good (pwK A e)
  | 0 => good_I22
  | e + 1 => by rw [pwK_succ]; exact good_mm (good_pw hA e) hA

theorem eqA_good {A B : ℕ} (hA : Good A) (hB : Good B) :
    eqA 2300 (permOfMat 22 co2FiveV A) (permOfMat 22 co2FiveV B) = Nat.beq A B := by
  have h := eqA_permOfMat spans hA.1 hB.1 hA.2 hB.2
  rwa [V_size] at h

theorem commA_good {A X : ℕ} (hA : Good A) (hX : Good X) :
    commA 2300 (permOfMat 22 co2FiveV A) (permOfMat 22 co2FiveV X) = comm A X := by
  have h := commA_permOfMat spans hA.1 hX.1
  rw [V_size, ← hmm, ← hmm] at h
  exact h

theorem pow_good {A : ℕ} (hA : Good A) (e : ℕ) :
    CFSG.Monster.B.Mathieu.powArr 2300 (permOfMat 22 co2FiveV A) e =
      permOfMat 22 co2FiveV (pwK A e) := pow_eq A hA.1 e

theorem conj_good {G G' Y : ℕ} (hG : Inv 22 co2FiveV G G') (hY : Good Y) :
    conjA 2300 (permOfMat 22 co2FiveV G) (permOfMat 22 co2FiveV Y) =
      permOfMat 22 co2FiveV (mmK (mmK G' Y) G) := by
  have h := conjA_permOfMat hd22 sys.nodup sys.lt hG hY.1
  rw [V_size] at h
  rw [h, hmm, hmm]

theorem compA_good {A B : ℕ} (hB : Good B) :
    compA 2300 (permOfMat 22 co2FiveV A) (permOfMat 22 co2FiveV B) =
      permOfMat 22 co2FiveV (mmK B A) := by
  have h := compA_permOfMat (V := co2FiveV) (A := A) hB.1
  rw [V_size] at h
  rw [h, hmm]

theorem invCand_good {A A' : ℕ} (h : Inv 22 co2FiveV A A') :
    invCand 2300 (permOfMat 22 co2FiveV A) = permOfMat 22 co2FiveV A' := by
  have e := invCand_permOfMat hd22 sys.nodup sys.lt h
  rwa [V_size] at e

theorem validA_inv {A A' : ℕ} (h : Inv 22 co2FiveV A A') :
    validA 2300 (permOfMat 22 co2FiveV A) = true := by
  have e := validA_permOfMat hd22 sys.nodup sys.lt h
  rwa [V_size] at e

theorem any_good {c : ArrCert} {N : ℕ} {PM : ℕ → ℕ} (hN : c.pts.size = N)
    (hP : ∀ i < N, c.pts[i]! = permOfMat 22 co2FiveV (PM i)) {A : ℕ} {j : ℕ} (hj : j < N)
    (he : PM j = A) : c.pts.toList.any (eqA 2300 (permOfMat 22 co2FiveV A)) = true := by
  rw [List.any_eq_true]
  refine ⟨c.pts[j]!, ?_, ?_⟩
  · rw [getElem!_pos c.pts _ (by rw [hN]; exact hj)]
    exact Array.getElem_mem_toList _
  · rw [hP j hj, he, eqA, allLt_iff]
    exact fun i _ => beq_self_eq_true _

theorem mask484 : mask 484 = M484 := by decide

theorem lit_facts {n g : ℕ} {MH EH RH LH : String} {csP csE csR csL : List Char}
    {FP FE FR FL : ℕ → ℕ} (hPs : MH = String.ofList csP) (hPa : hexFlat csP 121 1 484 n FP = true)
    (hEs : EH = String.ofList csE) (hEa : hexFlat csE 3 g 12 n FE = true)
    (hRs : RH = String.ofList csR) (hRa : hexFlat csR 3 n 12 1 FR = true)
    (hLs : LH = String.ofList csL) (hLa : hexFlat csL 3 n 12 1 FL = true) :
    let c : ArrCert := ⟨Array.ofFn fun i : Fin n =>
        permOfMat 22 co2FiveV (hexTable 121 1 i.val MH)[0]!,
      Array.ofFn fun i : Fin n => hexTable3 g (g * i.val) EH, hexTable3 n 0 RH, hexTable3 n 0 LH⟩
    c.pts.size = n ∧ (∀ i < n, c.pts[i]! = permOfMat 22 co2FiveV (Nat.land (FP i) M484)) ∧
      (∀ i < n, (c.edges[i]!).size = g ∧ ∀ k < g, (c.edges[i]!)[k]! = f12 (FE i) k) ∧
      (∀ i < n, c.par[i]! = f12 (FR 0) i ∧ c.lab[i]! = f12 (FL 0) i) := by
  intro c
  have hr : hexTable3 n 0 RH = unpack n 12 (FR 0) := by
    have h := hexTable3_sound hRa 0 (by norm_num)
    rwa [Nat.mul_zero, ← hRs] at h
  have hl : hexTable3 n 0 LH = unpack n 12 (FL 0) := by
    have h := hexTable3_sound hLa 0 (by norm_num)
    rwa [Nat.mul_zero, ← hLs] at h
  refine ⟨by simp [c], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · change (Array.ofFn fun i : Fin n => permOfMat 22 co2FiveV (hexTable 121 1 i.val MH)[0]!)[i]!
      = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
    have h := hexTable_sound hPa i hi
    rw [Nat.one_mul, ← hPs] at h
    rw [h, CFSG.KC.Misc.PairCount.unpack_get (by norm_num), ← mask484]
    rfl
  · have he : (Array.ofFn fun i : Fin n => hexTable3 g (g * i.val) EH)[i]! =
        unpack g 12 (FE i) := by
      rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn, hEs]
      exact hexTable3_sound hEa i hi
    change (Array.ofFn fun i : Fin n => hexTable3 g (g * i.val) EH)[i]!.size = g ∧ _
    rw [he]
    exact ⟨by simp [unpack], fun k hk => (CFSG.KC.Misc.PairCount.unpack_get hk).trans rfl⟩
  · change (hexTable3 n 0 RH)[i]! = _ ∧ (hexTable3 n 0 LH)[i]! = _
    rw [hr, hl]
    exact ⟨(CFSG.KC.Misc.PairCount.unpack_get hi).trans rfl,
      (CFSG.KC.Misc.PairCount.unpack_get hi).trans rfl⟩

theorem litQ : co2FiveQLit.pts.size = 125 ∧
    (∀ i < 125, co2FiveQLit.pts[i]! = permOfMat 22 co2FiveV (PQ i)) ∧
    (∀ i < 125, (co2FiveQLit.edges[i]!).size = 2 ∧
      ∀ k < 2, (co2FiveQLit.edges[i]!)[k]! = f12 (HQE.F i) k) ∧
    (∀ i < 125, co2FiveQLit.par[i]! = f12 (HQR.F 0) i ∧ co2FiveQLit.lab[i]! = f12 (HQL.F 0) i) := by
  unfold co2FiveQLit
  exact lit_facts HQP.eq HQP.all HQE.eq HQE.all HQR.eq HQR.all HQL.eq HQL.all

theorem litC0 : co2FiveC0Lit.pts.size = 3000 ∧
    (∀ i < 3000, co2FiveC0Lit.pts[i]! = permOfMat 22 co2FiveV (PC0 i)) ∧
    (∀ i < 3000, (co2FiveC0Lit.edges[i]!).size = 2 ∧
      ∀ k < 2, (co2FiveC0Lit.edges[i]!)[k]! = f12 (HC0E.F i) k) ∧
    (∀ i < 3000, co2FiveC0Lit.par[i]! = f12 (HC0R.F 0) i ∧
      co2FiveC0Lit.lab[i]! = f12 (HC0L.F 0) i) := by
  unfold co2FiveC0Lit
  exact lit_facts HC0P.eq HC0P.all HC0E.eq HC0E.all HC0R.eq HC0R.all HC0L.eq HC0L.all

theorem litC1 : co2FiveC1Lit.pts.size = 600 ∧
    (∀ i < 600, co2FiveC1Lit.pts[i]! = permOfMat 22 co2FiveV (PC1 i)) ∧
    (∀ i < 600, (co2FiveC1Lit.edges[i]!).size = 3 ∧
      ∀ k < 3, (co2FiveC1Lit.edges[i]!)[k]! = f12 (HC1E.F i) k) ∧
    (∀ i < 600, co2FiveC1Lit.par[i]! = f12 (HC1R.F 0) i ∧
      co2FiveC1Lit.lab[i]! = f12 (HC1L.F 0) i) := by
  unfold co2FiveC1Lit
  exact lit_facts HC1P.eq HC1P.all HC1E.eq HC1E.all HC1R.eq HC1R.all HC1L.eq HC1L.all

theorem litD : co2FiveDLit.pts.size = 60 ∧
    (∀ i < 60, co2FiveDLit.pts[i]! = permOfMat 22 co2FiveV (PD i)) ∧
    (∀ i < 60, (co2FiveDLit.edges[i]!).size = 2 ∧
      ∀ k < 2, (co2FiveDLit.edges[i]!)[k]! = f12 (HDE.F i) k) ∧
    (∀ i < 60, co2FiveDLit.par[i]! = f12 (HDR.F 0) i ∧ co2FiveDLit.lab[i]! = f12 (HDL.F 0) i) := by
  unfold co2FiveDLit
  exact lit_facts HDP.eq HDP.all HDE.eq HDE.all HDR.eq HDR.all HDL.eq HDL.all

end CertificateChecks.KernelMisc.Co2K

end
