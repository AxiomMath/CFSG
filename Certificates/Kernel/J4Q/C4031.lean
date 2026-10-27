module

public import CFSG.Sporadic.J4.QT2ANative
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4CzCheckInputs
public import Certificates.Kernel.J4Q.QT2AC
public import Certificates.Kernel.J4Q.X0
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

theorem heW_chk : andB (Nat.beq YA (wordJ c rm one G5 G5i aK))
    (andB (Nat.beq YB (wordJ c rm one G5 G5i bK))
      (andB (Nat.beq YC (wordJ c rm one G5 G5i (negRev aK ++ negRev bK ++ aK ++ bK)))
        (CFSG.KC.Enum.allN 4 fun k =>
          andB (Nat.beq (getN one QAs k) (wordJ c rm one G5 G5i (qGenK.getD k [])))
            (Nat.beq (getN one QIs k) (wordJ c rm one G5 G5i (negRev (qGenK.getD k []))))))) =
    true := by
  quickRfl

theorem he_encA : encR (wR aDw) = YA := by
  rw [(wR_enc _).2, aDw_eq]
  exact (Nat.eq_of_beq_eq_true (andB_true heW_chk).1).symm

theorem he_encB : encR (wR bDw) = YB := by
  rw [(wR_enc _).2, bDw_eq]
  exact (Nat.eq_of_beq_eq_true (andB_true (andB_true heW_chk).2).1).symm

theorem he_encC : encR (wR cDw) = YC := by
  rw [(wR_enc _).2, cDw, invW_eq, invW_eq, aDw_eq, bDw_eq]
  exact (Nat.eq_of_beq_eq_true (andB_true (andB_true (andB_true heW_chk).2).2).1).symm

theorem he_encQ {k : Nat} (hk : k < 4) :
    encR (qR k) = getN one QAs k ∧ encR (wR (invW (qGenW.getD k []))) = getN one QIs k := by
  have h := andB_true (CFSG.KS.allN_spec (andB_true (andB_true (andB_true heW_chk).2).2).2 k hk)
  refine ⟨?_, ?_⟩
  · rw [qR, (wR_enc _).2, qGenW_eq]
    exact (Nat.eq_of_beq_eq_true h.1).symm
  · rw [(wR_enc _).2, qGenW_eq, invW_eq]
    exact (Nat.eq_of_beq_eq_true h.2).symm

@[expose] noncomputable def heYK (n : Nat) : Nat :=
  mulJ c rm (mulJ c rm (powJ c rm one YA (n / 9)) (powJ c rm one YB (n / 3 % 3)))
    (powJ c rm one YC (n % 3))

theorem heY_enc (n : Nat) : WfA (yEl n) ∧ encR (yEl n) = heYK n := by
  have hA := (wR_enc aDw).1
  have hB := (wR_enc bDw).1
  have hC := (wR_enc cDw).1
  have h1 := wf_mulRows (wf_powRows hA (n / 9)) (wf_powRows hB (n / 3 % 3))
  refine ⟨wf_mulRows h1 (wf_powRows hC _), ?_⟩
  rw [yEl, enc_mulRows hK h1 (wf_powRows hC _), enc_mulRows hK (wf_powRows hA _) (wf_powRows hB _),
    enc_powRows hK hA, enc_powRows hK hB, enc_powRows hK hC, he_encA, he_encB, he_encC]
  rfl

@[expose] noncomputable def hcK (Q Qi y : Nat) : Nat :=
  mulJ c rm (mulJ c rm (mulJ c rm Q y) Qi) (mulJ c rm y y)

theorem heC_enc {k : Nat} (hk : k < 4) (n : Nat) :
    WfA (hCommRows k n) ∧ encR (hCommRows k n) = hcK (getN one QAs k) (getN one QIs k) (heYK n) := by
  obtain ⟨wy, ey⟩ := heY_enc n
  have wq : WfA (qR k) := (wR_enc (qGenW.getD k [])).1
  have wqi := (wR_enc (invW (qGenW.getD k []))).1
  obtain ⟨eq, eqi⟩ := he_encQ hk
  have w1 : WfA (mulRows (qR k) (yEl n)) := wf_mulRows wq wy
  have w2 := wf_mulRows w1 wqi
  refine ⟨wf_mulRows w2 (wf_mulRows wy wy), ?_⟩
  rw [hCommRows, enc_mulRows hK w2 (wf_mulRows wy wy), enc_mulRows hK w1 wqi,
    enc_mulRows hK wq wy, enc_mulRows hK wy wy, eq, eqi, ey]
  rfl

@[expose] noncomputable def prK (Q1 Q1i Q2 Q2i y : Nat) : Bool :=
  strictB (hcK Q1 Q1i y) fun h1 => strictB (hcK Q2 Q2i y) fun h2 =>
    neN (mulJ c rm h1 h2) (mulJ c rm h2 h1)

theorem pair_eq {i j : Nat} (hi : i < 4) (hj : j < 4) (n : Nat) :
    (wfR (hCommRows i n) && wfR (hCommRows j n) && nocomm (hCommRows i n) (hCommRows j n)) =
      prK (getN one QAs i) (getN one QIs i) (getN one QAs j) (getN one QIs j) (heYK n) := by
  obtain ⟨w1, e1⟩ := heC_enc hi n
  obtain ⟨w2, e2⟩ := heC_enc hj n
  have b1 : wfR (hCommRows i n) = true := wf_bool w1
  have b2 : wfR (hCommRows j n) = true := wf_bool w2
  rw [b1, b2, Bool.true_and, Bool.true_and, nocomm, eqRows_eq (wf_mulRows w1 w2) (wf_mulRows w2 w1),
    enc_mulRows hK w1 w2, enc_mulRows hK w2 w1, e1, e2, prK, strictB_eq, strictB_eq, neN_eq]

theorem cube_eq (n : Nat) : eqRows (mulRows (yEl n) (mulRows (yEl n) (yEl n))) idRows =
    Nat.beq (mulJ c rm (heYK n) (mulJ c rm (heYK n) (heYK n))) one := by
  obtain ⟨wy, ey⟩ := heY_enc n
  rw [eqRows_eq (wf_mulRows wy (wf_mulRows wy wy)) wf_idRows, enc_mulRows hK wy (wf_mulRows wy wy),
    enc_mulRows hK wy wy, ey, enc_idRows hK]

theorem he_chk : CFSG.KC.Enum.allN 27 (fun n => orB (Nat.beq n 0) (strictB (heYK n) fun y =>
    andB (Nat.beq (mulJ c rm y (mulJ c rm y y)) one)
      (orB (prK (getN one QAs 0) (getN one QIs 0) (getN one QAs 1) (getN one QIs 1) y)
        (orB (prK (getN one QAs 0) (getN one QIs 0) (getN one QAs 2) (getN one QIs 2) y)
          (prK (getN one QAs 0) (getN one QIs 0) (getN one QAs 3) (getN one QIs 3) y))))) = true := by
  quickRfl

theorem he_let : (qGenK.all fun w => w.all fun l => l != 0) = true := by
  quickRfl

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs in
open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A in
theorem c4031 : (chkHE = true) := by
  unfold chkHE
  rw [Bool.and_eq_true, qGenW_eq]
  refine ⟨he_let, ?_⟩
  rw [List.all_eq_true]
  intro n hn
  have h := CFSG.KS.allN_spec he_chk n (List.mem_range.1 hn)
  beta_reduce at h
  by_cases h0 : n = 0
  · subst h0
    rfl
  have hne : (n == 0) = false := by simp [h0]
  rw [nbeq_false h0, strictB_eq] at h
  rw [orB_eq, Bool.false_or, andB_eq, orB_eq, orB_eq] at h
  rw [hne, Bool.false_or, cube_eq]
  simp only [hePairs, List.any_cons, List.any_nil, Bool.or_false]
  rw [pair_eq (by decide) (by decide) n, pair_eq (by decide) (by decide) n,
    pair_eq (by decide) (by decide) n]
  exact h

end CertificateChecks.KernelJ4Q

end
