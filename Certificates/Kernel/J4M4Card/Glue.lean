module

public import Certificates.Kernel.J4M4Card.Checks
public import Certificates.Certificate7253
public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.Kernel.J4M4Card.Sound

public section

namespace CertificateChecks.KernelJ4M4Card

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KD.J4NPV CFSG.KD.J4M4F CFSG.KD.J4M4Card CFSG.KS.J4M4F
  CFSG.KS.J4M4Card CertificateChecks.KernelJ4Q CertificateChecks.KernelJ4M4F
  CFSG.Quasithin.KGC31.J4M4 CFSG.Quasithin.J4M4Card CFSG.Sporadic.J4.Native

open CFSG.Sporadic.J4.QT (uTab etaRows)

theorem strictB_eq7256 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem shl_one (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := by
  change 1 <<< k = 2 ^ k
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem g_enc : WfA (gRows ()) ∧ encR (gRows ()) = G7256 := by
  unfold gRows
  exact enc_wordRows hK base_gens base_invs gWord

theorem gi_enc : WfA (gInvRows ()) ∧ encR (gInvRows ()) = Gi7256 := by
  unfold gInvRows
  exact enc_wordRows hK base_gens base_invs (invW gWord)

theorem conj_enc (w : List Int) :
    WfA (mulRows (mulRows (gRows ()) (wordRows (m4Mats ()) (m4Invs ()) w)) (gInvRows ())) ∧
      encR (mulRows (mulRows (gRows ()) (wordRows (m4Mats ()) (m4Invs ()) w)) (gInvRows ())) =
        conjW c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] w := by
  have hw := enc_wordRows hK m4_enc m4i_enc w
  obtain ⟨g1, g2⟩ := g_enc
  obtain ⟨i1, i2⟩ := gi_enc
  refine ⟨wf_mulRows (wf_mulRows g1 hw.1) i1, ?_⟩
  rw [enc_mulRows hK (wf_mulRows g1 hw.1) i1, enc_mulRows hK g1 hw.1, g2, hw.2, i2]
  rfl

theorem mul3_enc {X Y Z : Array V2} (hX : WfA X) (hY : WfA Y) (hZ : WfA Z) :
    WfA (mulRows (mulRows X Y) Z) ∧
      encR (mulRows (mulRows X Y) Z) = mulJ c rm (mulJ c rm (encR X) (encR Y)) (encR Z) :=
  ⟨wf_mulRows (wf_mulRows hX hY) hZ, by rw [enc_mulRows hK (wf_mulRows hX hY) hZ, enc_mulRows hK hX hY]⟩

theorem slice {f : Nat → Bool} {lo n : Nat} (h : allR n (fun t => f (Nat.add lo t)) = true) :
    ∀ x, lo ≤ x → x < lo + n → f x = true := by
  intro x h1 h2
  have := allR_spec h (x - lo) (by omega)
  have e : Nat.add lo (x - lo) = x := by
    simp only [Nat.add_eq]
    omega
  rwa [e] at this

theorem mk_all : ∀ i < 62, masksAt c rm one Us7256
    (conjW c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] (schWord i))
    (conjW c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] (invW (schWord i))) (getLL maskTab i) = true := by
  intro i hi
  have key := fun lo n (h : mkK maskTab lo n = true) => slice (f := fun i => masksAt c rm one Us7256
    (conjW c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] (schWord i))
    (conjW c rm one G7256 Gi7256 [W1, W2] [W1i, W2i] (invW (schWord i))) (getLL maskTab i)) h i
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨
      (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 62)) with
    h | h | h | h | h | h | h | h
  · exact key 0 8 mk_ok0 (by omega) (by omega)
  · exact key 8 8 mk_ok1 h.1 (by omega)
  · exact key 16 8 mk_ok2 h.1 (by omega)
  · exact key 24 8 mk_ok3 h.1 (by omega)
  · exact key 32 8 mk_ok4 h.1 (by omega)
  · exact key 40 8 mk_ok5 h.1 (by omega)
  · exact key 48 8 mk_ok6 h.1 (by omega)
  · exact key 56 6 mk_ok7 h.1 (by omega)

theorem chkMasks_ok : chkMasks () = true := by
  unfold chkMasks chkMasksWith
  simp only [List.all_eq_true, List.mem_range]
  intro i hi k hk
  obtain ⟨h1, h2⟩ := conj_enc (schWord i)
  obtain ⟨i1, i2⟩ := conj_enc (invW (schWord i))
  obtain ⟨e1, e2⟩ := eta_enc (2 ^ k)
  obtain ⟨f1, f2⟩ := eta_enc ((maskTab.getD i []).getD k 0)
  obtain ⟨m1, m2⟩ := mul3_enc h1 e1 i1
  have hh : hRows i = mulRows (mulRows (gRows ()) (wordRows (m4Mats ()) (m4Invs ()) (schWord i)))
      (gInvRows ()) := rfl
  have hhi : hInvRows i = mulRows (mulRows (gRows ())
      (wordRows (m4Mats ()) (m4Invs ()) (invW (schWord i)))) (gInvRows ()) := rfl
  rw [hh, hhi, eqRows_eq m1 f1, m2, h2, e2, i2, f2]
  have hs := mk_all i hi
  unfold masksAt at hs
  rw [strictB_eq7256, strictB_eq7256] at hs
  have := allR_spec hs k hk
  rw [getN_eq', getLL_eq, shl_one] at this
  exact this

@[expose] noncomputable def wE7256 : Nat :=
  mulJ c rm (mulJ c rm Gi7256 (etaK c rm one Us7256 (Nat.shiftLeft 1 2))) G7256

theorem wit_all : ∀ x < 1024, neN (mulJ c rm (mulJ c rm wE7256 (getN one FMs7256 0)) wE7256)
    (fRK c rm one FMs7256 x) = true := by
  intro x hx
  have key := fun lo n (h : wtK 2 0 lo n = true) => by
    unfold wtK witChk at h
    rw [strictB_eq7256, strictB_eq7256] at h
    exact slice (f := fun x => neN (mulJ c rm (mulJ c rm wE7256 (getN one FMs7256 0)) wE7256)
      (fRK c rm one FMs7256 x)) h
  rcases (by omega : x < 128 ∨ (128 ≤ x ∧ x < 256) ∨ (256 ≤ x ∧ x < 384) ∨ (384 ≤ x ∧ x < 512) ∨
      (512 ≤ x ∧ x < 640) ∨ (640 ≤ x ∧ x < 768) ∨ (768 ≤ x ∧ x < 896) ∨ (896 ≤ x ∧ x < 1024)) with
    h | h | h | h | h | h | h | h
  · exact key 0 128 wit_ok0 x (by omega) (by omega)
  · exact key 128 128 wit_ok1 x h.1 (by omega)
  · exact key 256 128 wit_ok2 x h.1 (by omega)
  · exact key 384 128 wit_ok3 x h.1 (by omega)
  · exact key 512 128 wit_ok4 x h.1 (by omega)
  · exact key 640 128 wit_ok5 x h.1 (by omega)
  · exact key 768 128 wit_ok6 x h.1 (by omega)
  · exact key 896 128 wit_ok7 x h.1 (by omega)

theorem chkWit_ok : chkWit () = true := by
  unfold chkWit chkWitWith
  simp only [List.all_eq_true, List.mem_range]
  intro x hx
  obtain ⟨g1, g2⟩ := g_enc
  obtain ⟨i1, i2⟩ := gi_enc
  obtain ⟨e1, e2⟩ := eta_enc (2 ^ 2)
  obtain ⟨w1, w2⟩ := mul3_enc i1 e1 g1
  have hw : wRowsWith (uTab (locMats ()) (locInvs ())) =
      mulRows (mulRows (gInvRows ()) (etaRows (uTab (locMats ()) (locInvs ())) 11 (2 ^ 2)))
        (gRows ()) := rfl
  have hj : witJ = 0 := rfl
  obtain ⟨t1, t2⟩ := fTab_enc 0 (by decide)
  obtain ⟨x1, x2⟩ := mul3_enc w1 t1 w1
  obtain ⟨r1, r2⟩ := fRows_enc hK fTab_enc x
  rw [hw, hj]
  refine rowsDiffer_of_ne x1 r1 ?_
  rw [x2, w2, e2, g2, i2, t2, r2]
  have := wit_all x hx
  unfold wE7256 at this
  rw [shl_one] at this
  exact neN_spec this

theorem chkKE_ok : chkKE () = true := by
  unfold chkKE chkKEWith
  simp only [List.all_eq_true, List.mem_range]
  intro j hj
  have hw := enc_wordRows hK m4_enc m4i_enc (keWords.getD j [])
  obtain ⟨g1, g2⟩ := g_enc
  obtain ⟨i1, i2⟩ := gi_enc
  obtain ⟨e1, e2⟩ := eta_enc (keMasks.getD j 0)
  obtain ⟨m1, m2⟩ := mul3_enc i1 e1 g1
  have hg : geRowsWith (uTab (locMats ()) (locInvs ())) (keMasks.getD j 0) =
      mulRows (mulRows (gInvRows ()) (etaRows (uTab (locMats ()) (locInvs ())) 11
        (keMasks.getD j 0))) (gRows ()) := rfl
  rw [hg, eqRows_eq hw.1 m1, hw.2, m2, i2, e2, g2]
  exact keK_spec keWords keMasks ke_ok j hj

end CertificateChecks.KernelJ4M4Card

end
