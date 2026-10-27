module

public import CFSG.Sporadic.J4.QT2LocCntNative
public import Certificates.Kernel.J4Q.LocM
public import Certificates.Kernel.J4Q.Orb
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

@[expose] noncomputable def zcK (j : Nat) : Bool :=
  (fun c => decide (c < 2048) && letters.all fun ℓ => ZML.contains (act ℓ c)) (getN 0 ZML j)

#j4q_all CFSG.KD.J4Q.ZC CertificateChecks.KernelJ4Q.zcK 1771

theorem zml_len : Nat.beq ZML.length 1771 = true := by quickRfl

theorem zml_dist : distinctK ZML = true := by quickRfl

theorem zMasks_ok : chkZMasks = true := by
  have hlen := Nat.eq_of_beq_eq_true zml_len
  have h1 : (ZML.all fun c => decide (c < 2048) && letters.all fun ℓ => ZML.contains (act ℓ c)) =
      true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨j, hj, rfl⟩ := getN_of_mem 0 hc
    have hj' : j < 1771 := by rw [← hlen]; exact hj
    exact ZC.all j hj'
  have h2 : (ZML.length == 1771) = true := by rw [hlen]; rfl
  have h3 : decide ZML.Nodup = true := decide_eq_true (nodup_of_distinctK zml_dist)
  have h4 : ZML.contains 3 = true := by quickRfl
  have h5 : ZML.contains 1131 = true := by quickRfl
  have h6 : ((orbits.getD 1 (3, [], [])).1 == 3) = true := by quickRfl
  unfold chkZMasks
  rw [zMasks_ZML, h1, h2, h3, h4, h5, h6]
  rfl

@[expose] noncomputable def CZs : List (List Nat) := [CZ_0, CZ_1, CZ_2, CZ_3, CZ_4, CZ_5]

@[expose] noncomputable def boolEqK (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

theorem boolEqK_spec {a b : Bool} (h : boolEqK a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] noncomputable def zK (t : Nat) : Bool :=
  (fun i m => boolEqK (strictB (cvK i m) fun v => EVS.any fun u => notB (neN v u))
      ((CZs.getD i []).contains m))
    (Nat.div t 1771) (getN 0 ZML (Nat.mod t 1771))

#j4q_all CFSG.KD.J4Q.ZK CertificateChecks.KernelJ4Q.zK 10626

theorem any_congr_mem {α : Type} {f g : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.any f = l.any g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.any_cons, List.any_cons, h x List.mem_cons_self,
      any_congr_mem fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem candZ_len {i : Nat} (hi : i < 6) :
    (candZ (locMats ()) (locInvs ()) (1 + 1 * i)).length =
      (ZML.filter fun c => (CZs.getD i []).contains c).length := by
  have hlen := Nat.eq_of_beq_eq_true zml_len
  unfold candZ
  simp only []
  rw [zMasks_ZML]
  congr 1
  apply List.filter_congr
  intro m hm
  obtain ⟨j, hj, hjm⟩ := getN_of_mem 0 hm
  have hj' : j < 1771 := by rw [← hlen]; exact hj
  have hb : 1771 * i + j < 10626 := by omega
  have h2 := ZK.all (1771 * i + j) hb
  have hdiv : Nat.div (1771 * i + j) 1771 = i := by
    change (1771 * i + j) / 1771 = i
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hj', Nat.add_zero]
  have hmod : Nat.mod (1771 * i + j) 1771 = j := by
    change (1771 * i + j) % 1771 = j
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  rw [zK] at h2
  beta_reduce at h2
  rw [hdiv, hmod, hjm] at h2
  rw [← boolEqK_spec h2, strictB_eq]
  unfold memEVec evsOf
  simp only []
  obtain ⟨hwv, hvv⟩ := conjVec_enc hi m
  rw [EVS_eq, List.any_map, List.any_map]
  apply any_congr_mem
  intro c' hc'
  have h' : (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c').wf = true ∧
      v2N (etaVec ((uTab (locMats ()) (locInvs ())).map frTable) 11 c') = vecEtaK rm Us c' (v2N w0) :=
    v2N_etaVec hK uTab_enc (by simp [uTab, Us]) w0_wf c'
  change (!differs _ _) = notB (neN _ _)
  rw [differs_eq hwv h'.1, hvv, h'.2, notB_eq]

theorem candZ_len' (ℓ : Nat) (h1 : 1 ≤ ℓ) (h6 : ℓ ≤ 6) :
    (candZ (locMats ()) (locInvs ()) ℓ).length =
      (ZML.filter fun c => (CZs.getD (ℓ - 1) []).contains c).length := by
  obtain ⟨i, rfl⟩ : ∃ i, ℓ = 1 + 1 * i := ⟨ℓ - 1, by omega⟩
  have : 1 + 1 * i - 1 = i := by omega
  rw [this]
  exact candZ_len (by omega)

theorem cntZ_ok : chkCntZ (locMats ()) (locInvs ()) = true := by
  unfold chkCntZ
  rw [candZ_len' 1 (by decide) (by decide), candZ_len' 2 (by decide) (by decide),
    candZ_len' 3 (by decide) (by decide), candZ_len' 4 (by decide) (by decide),
    candZ_len' 5 (by decide) (by decide), candZ_len' 6 (by decide) (by decide)]
  quickRfl

theorem one_canon : andB (canonJ pad one) (Nat.beq (mulJ c rm one one) one) = true := by quickRfl

theorem pathInv_ok : ((List.range 7).all fun ℓ =>
    eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
      idRows) = true := by
  refine List.all_eq_true.2 fun ℓ hℓ => ?_
  have hℓ' := List.mem_range.1 hℓ
  rcases ℓ with _ | i
  · have h0 : pathRows (repPaths.getD 0 []) = idRows () := rfl
    rw [h0]
    have h := one_canon
    rw [andB_eq, Bool.and_eq_true] at h
    have hI := invRows_enc hK wf_idRows h.1 (by rw [enc_idRows hK]; exact h.2)
    rw [eqRows_of (mul_enc hK (id_enc hK) hI) (id_enc hK)]
    exact h.2
  · have : i + 1 = 1 + 1 * i := by omega
    rw [this]
    have hMi := pathMi_enc (i := i) (by omega)
    rw [eqRows_of (mul_enc hK (pathM_enc (by omega)) ⟨hMi.1, hMi.2.1⟩) (id_enc hK)]
    exact hMi.2.2

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT2 in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT in
theorem c4003 : (chkZMasks = true)
    ∧ (chkCntZ (locMats ()) (locInvs ()) = true)
    ∧ (vorbOK locTabs rep6Vec orb6 28336 = true)
    ∧ ((List.range 7).all (fun ℓ =>
          eqRows (mulRows (pathRows (repPaths.getD ℓ [])) (invRows (pathRows (repPaths.getD ℓ []))))
            idRows) = true) := ⟨zMasks_ok, cntZ_ok, orb6_vorbOK, pathInv_ok⟩

end CertificateChecks.KernelJ4Q

end
